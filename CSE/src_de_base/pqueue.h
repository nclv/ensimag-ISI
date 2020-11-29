#ifndef __PQUEUE_H_
#define __PQUEUE_H_

#include "processus.h"

typedef struct pqueue {
    process_t *head;
    size_t len;
} pqueue_t;

extern void print_queue(pqueue_t *pqueue);
extern pqueue_t *create_pqueue(void);
extern process_t *peek(pqueue_t *pqueue);
extern process_t *pop(pqueue_t *pqueue);
extern void push(pqueue_t *pqueue, process_t *process);
extern int is_empty(pqueue_t *pqueue);

#endif