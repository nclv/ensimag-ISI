#include "processus.h"

#include <stdio.h>
#include <string.h>

#include "cpu.h"

process_t processes_table[PROCESS_COUNT];
static int64_t pid = -1;

void idle(void) {
    printf("[idle] je tente de passer la main a proc1...\n");
    uint32_t *current_registers = processes_table[0].registers;
    uint32_t *new_registers = processes_table[1].registers;
    ctx_sw(current_registers, new_registers);
    printf("[idle] proc1 m'a redonne la main --'\n");
}

void proc1(void) {
    printf("[proc1] idle m'a donne la main\n");
    printf("[proc1] je tente de passer la main a idle...\n");
    uint32_t *current_registers = processes_table[1].registers;
    uint32_t *new_registers = processes_table[0].registers;
    ctx_sw(current_registers, new_registers);
    // printf("[proc1] j'arrete le systeme\n");
    // hlt();
}

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
    idle->pid = pid++;
    snprintf(idle->name, sizeof(idle->name), "%s", "idle");
    idle->state = RUNNING;

    /** 
     * La case de la zone de sauvegarde des registres correspondant à %esp (ie. deuxième case)
     * doit pointer sur le sommet de pile, et la case en sommet de pile doit contenir l’adresse 
     * de la fonction proc1.
     */
    process_t *proc1_t = &processes_table[1];
    proc1_t->pid = pid++;
    snprintf(proc1_t->name, sizeof(proc1_t->name), "%s", "proc1");
    proc1_t->state = READY_TO_RUN;
    proc1_t->registers[1] = (uint32_t)&proc1_t->stack[STACK_CAPACITY - 1];
    proc1_t->stack[STACK_CAPACITY - 1] = (uint32_t)proc1;
}