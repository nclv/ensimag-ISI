#include "stdio.h"
#include "string.h"

#include "pqueue.h"
#include "processus.h"
#include "malloc.h"

void print_queue(pqueue_t *pqueue) {
    process_t *process = pqueue->head;
    printf("Len: %d\n", pqueue->len);
    while (process != NULL) {
        print_process(process);
        process = process->next;
    }
}

pqueue_t *create_pqueue(void) {
    pqueue_t *pqueue = malloc(sizeof *pqueue);
    // if (pqueue == NULL) exit(EXIT_FAILURE);
    pqueue->head = NULL;
    pqueue->len = 0;

    return pqueue;
}

process_t *peek(pqueue_t *pqueue) {
    return pqueue->head;
}

process_t *pop(pqueue_t *pqueue) {
    process_t *process = pqueue->head;
    if (pqueue->head != NULL) pqueue->head = pqueue->head->next;
    if (pqueue->len-- <= 0) pqueue->len = 0;
    return process;
}

void push(pqueue_t *pqueue, process_t *process) {
    process_t *current_node = pqueue->head;
    process->next = NULL;
    if (pqueue->len == 0) {
        pqueue->head = process;
    } else if (current_node->priority > process->priority) {
        // insertion en tête
        process->next = pqueue->head;
        pqueue->head = process;
    } else {
        while (current_node->next != NULL && current_node->next->priority < process->priority) {
            current_node = current_node->next;
        }
        // end of the list or at good position
        process->next = current_node->next;
        current_node->next = process;
    }
    pqueue->len++;
}

int is_empty(pqueue_t *pqueue) {
    return (pqueue->head == NULL);
}