#include "processus.h"

#include <stdio.h>
#include <string.h>

#include "cpu.h"

#define PROCESS_COUNT (2)

process_t processes_table[PROCESS_COUNT];
/* Pointeur vers le processus actif dans processes_table */
process_t *active;

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
static void scheduler(void) {
    int64_t current_pid = get_active_pid();
    /* On loop sur chaque process à la suite */
    int64_t new_pid = (current_pid + 1) % PROCESS_COUNT;

    process_t *current_process = &processes_table[current_pid];
    process_t *new_process = &processes_table[new_pid];

    current_process->state = READY_TO_RUN;
    new_process->state = RUNNING;

    active = new_process;

    ctx_sw(current_process->registers, new_process->registers);
}

void idle(void) {
    // for (size_t i = 0; i < 3; ++i) {
    //     printf("[idle] je tente de passer la main a proc1...\n");
    //     uint32_t *current_registers = processes_table[0].registers;
    //     uint32_t *new_registers = processes_table[1].registers;
    //     ctx_sw(current_registers, new_registers);
    //     printf("[idle] proc1 m'a redonne la main --'\n");
    // }

    // for (;;) {
    for (size_t i = 0; i < 3; ++i) {
        printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        scheduler();
    }
    printf("[idle] j'arrete le systeme\n");
    hlt();
}

static void proc1(void) {
    // for (;;) {
    //     printf("[proc1] idle m'a donne la main\n");
    //     printf("[proc1] je tente de passer la main a idle...\n");
    //     uint32_t *current_registers = processes_table[1].registers;
    //     uint32_t *new_registers = processes_table[0].registers;
    //     ctx_sw(current_registers, new_registers);
    // }
    // printf("[proc1] j'arrete le systeme\n");
    // hlt();

    for (;;) {
        printf("[%s] pid = %lli\n", get_active_name(), get_active_pid());
        scheduler();
    }
}

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
    process_t *idle = &processes_table[0];
    idle->pid = ++pid;
    snprintf(idle->name, sizeof(idle->name), "%s", "idle");
    idle->state = RUNNING;
    // idle est le process actif
    active = idle;

    /** 
     * La case de la zone de sauvegarde des registres correspondant à %esp (ie. deuxième case)
     * doit pointer sur le sommet de pile, et la case en sommet de pile doit contenir l’adresse 
     * de la fonction proc1.
     */
    process_t *proc1_t = &processes_table[1];
    proc1_t->pid = ++pid;
    snprintf(proc1_t->name, sizeof(proc1_t->name), "%s", "proc1");
    proc1_t->state = READY_TO_RUN;
    proc1_t->registers[1] = (uint32_t)&proc1_t->stack[STACK_CAPACITY - 1];
    proc1_t->stack[STACK_CAPACITY - 1] = (uint32_t)proc1;
}