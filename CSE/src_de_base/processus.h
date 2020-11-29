#ifndef __PROCESSUS_H__
#define __PROCESSUS_H__

#include <inttypes.h>
#include <stddef.h>

#define MAX_LEN (100)
/**
 * Puisqu’on manipule des registres 32 bits, et vous avez besoin de 5 cases car il n’y a 
 * que 5 registres importants à sauvegarder sur x86
 */
#define NUM_REG (5)
#define STACK_CAPACITY (512)

typedef enum {
    RUNNING,
    READY_TO_RUN,
    SLEEPING,
    DEAD,
} state_t;

typedef struct process {
    int64_t pid;  // signed int return -1 if error
    char name[MAX_LEN];
    state_t state;
    uint32_t awake_in;
    uint32_t registers[NUM_REG];     // zone de sauvegarde des registres du processeur
    uint32_t stack[STACK_CAPACITY];  // pile d’exécution du processus,
    int priority;
    struct process *next;
} process_t;

extern void print_process(process_t *process);

extern void idle(void);
extern void init_processes(void);
extern void scheduler(void);
extern int32_t cree_processus(void (*proc)(void), char *name);
extern int sleep(uint32_t nbr_secs);
extern void kill(void);

// Assembly function
extern void ctx_sw(uint32_t *current_process, uint32_t *new_process);

#endif