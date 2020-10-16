#ifndef __PROCESSUS_H__
#define __PROCESSUS_H__

#include <inttypes.h>

#define MAX_LEN (100)
/**
 * Puisqu’on manipule des registres 32 bits, et vous avez besoin de 5 cases car il n’y a 
 * que 5 registres importants à sauvegarder sur x86
 */
#define NUM_REG (5)
#define STACK_CAPACITY (512)
#define PROCESS_COUNT (2)

typedef enum {
    RUNNING,
    READY_TO_RUN,
} state_t;

typedef struct process {
    int64_t pid;  // signed int return -1 if error
    char name[MAX_LEN];
    state_t state;
    uint32_t registers[NUM_REG];     // zone de sauvegarde des registres du processeur
    uint32_t stack[STACK_CAPACITY];  // pile d’exécution du processus,
} process_t;

extern void idle(void);
extern void init_processes(void);

extern void scheduler(void);

// Assembly function
extern void ctx_sw(uint32_t *current_process, uint32_t *new_process);

#endif