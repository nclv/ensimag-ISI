#include "processus.h"

#include <stdio.h>
#include <string.h>

#include "cpu.h"
#include "idt.h"
#include "malloc.h"
#include "pqueue.h"

#define PROCESS_COUNT (8)

process_t processes_table[PROCESS_COUNT];

/* Pointeur vers le processus actif dans processes_table */
process_t *active = NULL;
pqueue_t *pqueue_ready_to_run = NULL;
pqueue_t *pqueue_sleeping = NULL;
pqueue_t *pqueue_dead = NULL;

/* On incrémente le pid à chaque nouveau process */
static int64_t pid = -1;

void print_process(process_t *process) {
    printf("Name: %s, State: %d, Priority: %d, Awake in: %d, PID: %lld\n", process->name, process->state, process->priority, process->awake_in, process->pid);
}

/**
 * @return active process name
 */
static inline char *get_active_name(void) {
    if (active != NULL) {
        return active->name;
    }
    return (char *)-1;
}

/**
 * @return active process PID
 */
static inline int64_t get_active_pid(void) {
    if (active != NULL) {
        return active->pid;
    }
    return -1;
}

/**
 * Implémente la politique d’ordonnancement en choisissant le prochain processus à activer et
 * provoque le changement de processus.
 * 
 * @pre ctx_sw(), get_active_pid(), processes_table and PROCESS_COUNT are defined.
 */
void round_robin_scheduler(void) {
    // récupération du processus actif
    int64_t current_pid = get_active_pid();
    process_t *current_process = &processes_table[current_pid];

    // Mise à jour de l'état SLEEPING de tous les processus.
    for(int i = 1; i < PROCESS_COUNT; ++i){
        process_t *proc = &processes_table[i];
        if(proc->awake_in < get_uptime() && proc->state == SLEEPING){
            proc->state = READY_TO_RUN;
        }
    }

    /* On loop sur chaque process à la suite */
    int64_t new_pid = (current_pid + 1) % PROCESS_COUNT;
    process_t *new_process = &processes_table[new_pid];

    // On prend le prochain processus READY_TO_RUN
    while (new_pid != current_pid && new_process->state != READY_TO_RUN){
        new_pid = (new_pid + 1) % PROCESS_COUNT;
        new_process = &processes_table[new_pid];
    }

    if (current_process->state == RUNNING) {
        current_process->state = READY_TO_RUN;
    }
    new_process->state = RUNNING;

    active = new_process;

    ctx_sw(current_process->registers, new_process->registers);
}

/* Round-Robin scheduler with priority and dynamic processes */
void priority_scheduler(void) {
    // free dead processes
    process_t *current;
    while ((current = pop(pqueue_dead)) != NULL) {
        current = current->next;
        free(current);
    }

    // update sleeping processes
    while ((current = peek(pqueue_sleeping)) != NULL && current->awake_in < get_uptime()) {
        current->state = READY_TO_RUN;
        // add current current to READY_TO_RUN queue and remove from SLEEPING queue
        pop(pqueue_sleeping);
        push(pqueue_ready_to_run, current);
        current = current->next;
    }

    // do nothing if there is no READY_TO_RUN process
    if ((current = pop(pqueue_ready_to_run)) != NULL) {
        if (active->state == RUNNING) {
            active->state = READY_TO_RUN;
            push(pqueue_ready_to_run, active);
        }
        current->state = RUNNING;

        process_t *current_process = active;
        active = current;

        ctx_sw(current_process->registers, current->registers);
    }
}

void scheduler(void) {
    priority_scheduler();
}

int round_robin_sleep(uint32_t nbr_secs) {
    int64_t current_pid = get_active_pid();
    if (current_pid == 0) {
        // on ne peut pas endormir le processus idle
        return -1;
    }
    process_t *current_process = &processes_table[current_pid];
    current_process->state = SLEEPING;
    current_process->awake_in = get_uptime() + nbr_secs;
    current_process->priority = (int)current_process->awake_in;
    round_robin_scheduler();
    return 0;
}

int priority_sleep(uint32_t nbr_secs) {
    int64_t current_pid = get_active_pid();
    if (current_pid == 0) {
        // on ne peut pas endormir le processus idle
        return -1;
    }
    
    active->state = SLEEPING;
    active->awake_in = get_uptime() + nbr_secs;
    active->priority = (int)active->awake_in;
    push(pqueue_sleeping, active);
    priority_scheduler();
    return 0;
}

/**
 * Endors le processus courant.
 * 
 * @param nbr_secs
 * @return -1 if failure, else 0
 */
int sleep(uint32_t nbr_secs) {
    return priority_sleep(nbr_secs);
}

void round_robin_kill(void) {
    active->state = DEAD;
    --pid;
    round_robin_scheduler();
}

void priority_kill(void) {
    active->state = DEAD;
    --pid;
    push(pqueue_dead, active);
    priority_scheduler();
}

void kill(void) {
    priority_kill();
}

int32_t cree_processus_round_robin(void (*proc)(void), char *name) {
    if (pid == PROCESS_COUNT - 1 || name == NULL) {
        return -1;
    }
    int32_t my_pid = (int32_t)++pid;

    process_t *process = &processes_table[my_pid];
    process->pid = my_pid;
    snprintf(process->name, sizeof(process->name), "%s", name);
    process->state = READY_TO_RUN;
    process->awake_in = 0;
    process->next = NULL;
    process->priority = READY_TO_RUN;
    process->registers[1] = (uint32_t)&process->stack[STACK_CAPACITY - 2];
    process->stack[STACK_CAPACITY - 1] = (uint32_t)kill;
    process->stack[STACK_CAPACITY - 2] = (uint32_t)proc;

    return my_pid;
}

int32_t cree_processus_priority(void (*proc)(void), char *name) {
    if (pid == PROCESS_COUNT - 1 || name == NULL) {
        return -1;
    }
    int32_t my_pid = (int32_t)++pid;

    process_t *process = malloc(sizeof *process);
    process->pid = my_pid;
    snprintf(process->name, sizeof(process->name), "%s", name);
    process->state = READY_TO_RUN;
    process->awake_in = 0;
    process->next = NULL;
    process->priority = READY_TO_RUN;
    process->registers[1] = (uint32_t)&process->stack[STACK_CAPACITY - 2];
    process->stack[STACK_CAPACITY - 1] = (uint32_t)kill;
    process->stack[STACK_CAPACITY - 2] = (uint32_t)proc;

    push(pqueue_ready_to_run, process);

    return my_pid;
}

/**
 * Création d'un processus.
 *   
 * La case de la zone de sauvegarde des registres correspondant à %esp (ie. deuxième case)
 * doit pointer sur le sommet de pile, et la case en sommet de pile doit contenir l’adresse 
 * de la fonction proc1. L'avant dernière case contient la fonction de terminaison des processus.
 *
 * @param proc fonction du processus
 * @param name nom du processus créer
 * 
 * @return created processus pid, else -1
 */
int32_t cree_processus(void (*proc)(void), char *name) {
    return cree_processus_priority(proc, name);
}

void idle(void) {
    // for (size_t i = 0; i < 3; ++i) {
    //     printf("[idle] je tente de passer la main a proc1...\n");
    //     uint32_t *current_registers = processes_table[0].registers;
    //     uint32_t *new_registers = processes_table[1].registers;
    //     ctx_sw(current_registers, new_registers);
    //     printf("[idle] proc1 m'a redonne la main --'\n");
    // }

    for (;;) {
    // for (size_t i = 0; i < 20; ++i) {
        // printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        // scheduler();
        sti();
        hlt();
        cli();
    }
    printf("[idle] j'arrete le systeme\n");
    hlt();
}

void proc1(void) {
    // for (;;) {
    //     printf("[proc1] idle m'a donne la main\n");
    //     printf("[proc1] je tente de passer la main a idle...\n");
    //     uint32_t *current_registers = processes_table[1].registers;
    //     uint32_t *new_registers = processes_table[0].registers;
    //     ctx_sw(current_registers, new_registers);
    // }
    // printf("[proc1] j'arrete le systeme\n");
    // hlt();

    // for (;;) {
    for (size_t i = 0; i < 2; ++i) {
        printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        // printf("sleeping\n");
        // print_queue(pqueue_sleeping);
        // printf("ready_to_run\n");
        // print_queue(pqueue_ready_to_run);
        // printf("dead\n");
        // print_queue(pqueue_dead);
        // scheduler();
        sti();
        hlt();
        cli();

        sleep(2);
    }
    printf("[proc1] I kill myself\n");
    kill(); // mais on n'en a pas besoin grâce à la terminaison automatique
}

void proc2(void) {
    for (;;) {
        printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        // scheduler();
        sti();
        hlt();
        cli();
        sleep(3);
    }
}

void proc3(void) {
    for (;;) {
        printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        // scheduler();
        sti();
        hlt();
        cli();
        sleep(5);
    }
}

void proc4(void) {
    for (;;) {
        printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        // scheduler();
        printf("I kill myself\n");
        kill();
        sti();
        hlt();
        cli();
    }
}

void proc5(void) {
    for (;;) {
        printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        // scheduler();
        printf("je cree un nouveau processus\n");
        char *name = (char *)"new_process";
        int32_t proc_pid = cree_processus(proc4, name);
        if (proc_pid == -1) {
            printf("ERROR: %s cannot be created", name);
        }
        printf("I kill myself\n");
        kill();
        sti();
        hlt();
        cli();
    }
}

void proc6(void) {
    for (;;) {
        printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        // scheduler();
        printf("I kill myself\n");
        kill();
        sti();
        hlt();
        cli();
    }
}

void proc7(void) {
    for (size_t i = 0; i < 5; ++i) {
        printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        // scheduler();
        printf("I kill myself\n");
        kill();
        sti();
        hlt();
        cli();
    }
}

char proc_str[PROCESS_COUNT - 1][6] = {
    "proc1",
    "proc2",
    "proc3",
    "proc4",
    "proc5",
    "proc6",
    "proc7"
};

void (*proc_fn[PROCESS_COUNT - 1])(void) = {
    proc1,
    proc2,
    proc3,
    proc4,
    proc5,
    proc6,
    proc7,
};

/**
 * Initialisation des processus.
 * 
 * @pre processes_table, active, pid and STACK_CAPACITY are defined
 */
void init_processes(void) {
    /** 
     * idle is the first element of processes_table
     * Il n’est pas nécessaire d’initialiser la pile d’exécution du processus idle: en fait, 
     * ce processus n’utilisera pas la pile allouée dans sa structure de processus mais 
     * directement la pile du noyau (celle qui est utilisée parla fonction kernel_start 
     * notamment). De même, il n’est pas nécessaire d’initialiser la zone de 
     * sauvegarde de %esp pour idle puisque ce processus sera exécuté directement par la 
     * fonction kernel_start.
     */
    pqueue_ready_to_run = create_pqueue();
    pqueue_sleeping = create_pqueue();
    pqueue_dead = create_pqueue();

    // process_t *idle = &processes_table[pid];  // for static allocation
    process_t *idle = malloc(sizeof *idle);

    ++pid;
    idle->pid = pid;
    snprintf(idle->name, sizeof(idle->name), "%s", "idle");
    idle->state = RUNNING;
    idle->awake_in = 0;
    idle->next = NULL;
    idle->priority = __INT_MAX__;

    // idle est le process actif
    active = idle;

    /* Création des processus */

    int32_t proc_pid;
    for (int i = 0; i < PROCESS_COUNT - 1; i++) {
        proc_pid = cree_processus(*proc_fn[i], (char *)proc_str[i]);
        if (proc_pid == -1) {
            printf("ERROR: %s cannot be created", proc_str[i]);
        }
    }

    print_queue(pqueue_ready_to_run);
}