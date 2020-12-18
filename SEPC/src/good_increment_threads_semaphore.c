#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>

/*
Implémentation d'un mutex avec un sémaphore
*/

#define THSHARED (0)

sem_t sem;

void equiv_mutex_init(void) {
    sem_init(&sem, THSHARED, 1);
}

void equiv_mutex_lock(sem_t* s) {
    sem_wait(s); // P()
}

void equiv_mutex_unlock(sem_t* s) {
    sem_post(s);
}

static int compteur = 0;
void incremente(void) {
    equiv_mutex_lock(&sem);
    compteur++;
    equiv_mutex_unlock(&sem);
}

int loop(void* arg) {
    void (*f)(void) = (void (*)(void))arg;
    for (int i = 0; i < 1000000; ++i) {
        f();
    }
    return EXIT_SUCCESS;
}

int main(void) {
    thrd_t th1, th2;
    equiv_mutex_init();
    thrd_create(&th1, loop, (void*)incremente);
    thrd_create(&th2, loop, (void*)incremente);
    thrd_join(th1, 0);
    thrd_join(th2, 0);
    printf("compteur incrémenté: %d/2000000\n", compteur);
    return EXIT_SUCCESS;
}