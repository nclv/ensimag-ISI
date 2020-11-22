#include "processus.h"

#include <stdio.h>
#include <string.h>

#include "cpu.h"
#include "idt.h"
#include "malloc.c.h"

/** 
 * pqueue module
 * on est obligé de le mettre ici car il utilise malloc.c.h
 * il est explicitement écrit que malloc.c.h ne doit pas être 'include' dans un autre fichier
 * il faudrait modifier le Makefile pour que cela devienne possible
 */

static node_t *create_node(process_t *process, int priority) {
    node_t *node = malloc(sizeof(*node));
    // if (node == NULL) exit(EXIT_FAILURE);

    node->process = process;
    node->priority = priority;
    // node->previous = NULL;
    node->next = NULL;

    return node;
}

pqueue_t *create_pqueue(void) {
    pqueue_t *pqueue = malloc(sizeof(*pqueue));
    // if (pqueue == NULL) exit(EXIT_FAILURE);
    pqueue->head = NULL;

    return pqueue;
}

node_t *peek(pqueue_t *pqueue) {
    return pqueue->head;
}

void pop(pqueue_t *pqueue) {
    node_t *temp = pqueue->head;
    pqueue->head = pqueue->head->next;
    free(temp);
}

void push(pqueue_t *pqueue, process_t *process, int priority) {
    node_t *current_node = pqueue->head;
    node_t *new_node = create_node(process, priority);
    if (current_node == NULL) {
        new_node->next = NULL;
        pqueue->head = new_node;
    } else if (current_node->priority > new_node->priority) {
        // insertion en tête
        new_node->next = pqueue->head;
        // new_node->previous = NULL;
        // if (pqueue->head != NULL) pqueue->head->previous = new_node;
        pqueue->head = new_node;
    } else {
        while (current_node->next != NULL && current_node->next->priority < new_node->priority) {
            current_node = current_node->next;
        }
        // end of the list or at good position
        new_node->next = current_node->next;
        current_node->next = new_node;
        // new_node->previous = current_node;
        // if (new_node->next != NULL) new_node->next->previous = new_node;
    }
}

int is_empty(pqueue_t *pqueue) {
    return (pqueue->head == NULL);
}


void print_process(process_t *process) {
    printf("\nName: %s, State: %d, Awake in: %d, PID: %lld\n", process->name, process->state, process->awake_in, process->pid);
}

void print_queue(pqueue_t *pqueue) {
    node_t *node = pqueue->head;
    while (node != NULL) {
        print_process(node->process);
        printf("Priority: %d", node->priority);
        node = node->next;
    }
}

/* Processes handling */

#define PROCESS_COUNT (8)

process_t processes_table[PROCESS_COUNT];

/* Pointeur vers le processus actif dans processes_table */
process_t *active;
pqueue_t *pqueue_ready_to_run;
pqueue_t *pqueue_sleeping;
pqueue_t *pqueue_dead;

/* On incrémente le pid à chaque nouveau process */
static int64_t pid = -1;

/**
 * @return active process name
 */
static inline char *get_active_name(void) {
    return active->name;
}

/**
 * @return active process PID
 */
static inline int64_t get_active_pid(void) {
    return active->pid;
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

/* No processes_table */
void priority_scheduler(void) {
    // récupération du processus actif
    int64_t current_pid = get_active_pid();

    // free dead processes
    node_t *current = peek(pqueue_dead);
    while (current != NULL) {
        pop(pqueue_dead);
        free(current->process);
        current = current->next;
    }

    // update sleeping processes
    while ((current = peek(pqueue_sleeping)) != NULL && current->process->awake_in < get_uptime()) {
        process_t *process = current->process;
        process->state = READY_TO_RUN;
        // add current process to READY_TO_RUN queue
        push(pqueue_ready_to_run, process, READY_TO_RUN);
        // remove current from SLEEPING queue
        pop(pqueue_sleeping);
        current = current->next;
    }

    // do nothing if there is no READY_TO_RUN process
    if ((current = peek(pqueue_ready_to_run)) != NULL) {
        process_t *new_process = current->process;
        pop(pqueue_ready_to_run);
        if (active->state == RUNNING) {
            active->state = READY_TO_RUN;
            push(pqueue_ready_to_run, active, READY_TO_RUN);
        }
        new_process->state = RUNNING;

        ctx_sw(active->registers, new_process->registers);
        active = new_process;
    }
}

void scheduler(void) {
    round_robin_scheduler();
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
    push(pqueue_sleeping, active, active->awake_in);
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
    return round_robin_sleep(nbr_secs);
}

void round_robin_kill(void) {
    active->state = DEAD;
    round_robin_scheduler();
}

void priority_kill(void) {
    active->state = DEAD;
    push(pqueue_dead, active, DEAD);
    priority_scheduler();
}

void kill(void) {
    round_robin_kill();
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
        // print_queue(pqueue_sleeping);
        // print_queue(pqueue_ready_to_run);
        // print_queue(pqueue_dead);
        // scheduler();
        sti();
        hlt();
        cli();
        sleep(2);
    }
    printf("[proc1] I kill myself\n");
    kill();
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
        // printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        // scheduler();
        sti();
        hlt();
        cli();
    }
}

void proc5(void) {
    for (;;) {
        // printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        // scheduler();
        sti();
        hlt();
        cli();
    }
}

void proc6(void) {
    for (;;) {
        // printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        // scheduler();
        sti();
        hlt();
        cli();
    }
}

void proc7(void) {
    for (;;) {
        // printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        // scheduler();
        sti();
        hlt();
        cli();
    }
}

int32_t cree_processus_round_robin(void (*proc)(void), char *name) {
    int32_t my_pid = (int32_t)++pid;
    if (my_pid == PROCESS_COUNT) {
        return -1;
    }

    /** 
     * La case de la zone de sauvegarde des registres correspondant à %esp (ie. deuxième case)
     * doit pointer sur le sommet de pile, et la case en sommet de pile doit contenir l’adresse 
     * de la fonction proc1.
     */
    process_t *process = &processes_table[my_pid];
    process->pid = my_pid;
    snprintf(process->name, sizeof(process->name), "%s", name);
    process->state = READY_TO_RUN;
    process->awake_in = 0;
    process->registers[1] = (uint32_t)&process->stack[STACK_CAPACITY - 1];
    process->stack[STACK_CAPACITY - 1] = (uint32_t)proc;

    return my_pid;
}

int32_t cree_processus_priority(void (*proc)(void), char *name) {
    int32_t my_pid = (int32_t)++pid;
    if (my_pid == PROCESS_COUNT) {
        return -1;
    }

    /** 
     * La case de la zone de sauvegarde des registres correspondant à %esp (ie. deuxième case)
     * doit pointer sur le sommet de pile, et la case en sommet de pile doit contenir l’adresse 
     * de la fonction proc1.
     */
    process_t *process = malloc(sizeof(process));
    process->pid = my_pid;
    snprintf(process->name, sizeof(process->name), "%s", name);
    process->state = READY_TO_RUN;
    process->awake_in = 0;
    process->registers[1] = (uint32_t)&process->stack[STACK_CAPACITY - 1];
    process->stack[STACK_CAPACITY - 1] = (uint32_t)proc;

    return my_pid;
}

/**
 * Création d'un processus.
 * 
 * @param proc fonction du processus
 * @param name nom du processus créer
 * 
 * @return created processus pid, else -1
 */
int32_t cree_processus(void (*proc)(void), char *name) {
    return cree_processus_round_robin(proc, name);
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

    process_t *idle = &processes_table[++pid];  // for static allocation
    // malloc ne fonctionne pas sur WSL
    // process_t *idle = (process_t *)malloc(sizeof(idle));
    idle->pid = pid;
    snprintf(idle->name, sizeof(idle->name), "%s", "idle");
    idle->state = RUNNING;
    idle->awake_in = 0;
    // idle est le process actif
    active = idle;
    print_process(active);

    // pqueue_ready_to_run = create_pqueue();
    // pqueue_sleeping = create_pqueue();
    // pqueue_dead = create_pqueue();

    /* Création des processus */

    // problème avec l'argument *proc_fn[i]
    // int32_t proc_pid;
    // for (int i = 0; i < PROCESS_COUNT - 1; i++) {
    //     proc_pid = cree_processus(*proc_fn[i], (char *)proc_str[i]);
    //     print_process(&processes_table[proc_pid]);
    //     if (proc_pid == -1) {
    //         printf("ERROR: %s cannot be created", proc_str[i]);
    //     }
    // }

    char *name = (char *)"proc1";
    int32_t proc_pid;
    proc_pid = cree_processus(proc1, name);
    if (proc_pid == -1) {
        printf("ERROR: %s cannot be created", name);
    }

    name = (char *)"proc2";
    proc_pid = cree_processus(proc2, name);
    if (proc_pid == -1) {
        printf("ERROR: %s cannot be created", name);
    }
    name = (char *)"proc3";
    proc_pid = cree_processus(proc3, name);
    if (proc_pid == -1) {
        printf("ERROR: %s cannot be created", name);
    }
    name = (char *)"proc4";
    proc_pid = cree_processus(proc4, name);
    if (proc_pid == -1) {
        printf("ERROR: %s cannot be created", name);
    }
    name = (char *)"proc5";
    proc_pid = cree_processus(proc5, name);
    if (proc_pid == -1) {
        printf("ERROR: %s cannot be created", name);
    }
    name = (char *)"proc6";
    proc_pid = cree_processus(proc6, name);
    if (proc_pid == -1) {
        printf("ERROR: %s cannot be created", name);
    }
    name = (char *)"proc7";
    proc_pid = cree_processus(proc7, name);
    if (proc_pid == -1) {
        printf("ERROR: %s cannot be created", name);
    }
}