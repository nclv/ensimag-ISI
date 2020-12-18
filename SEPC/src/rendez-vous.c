#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>
#include <unistd.h>

/*
Rendez-vous: appariement entre deux classes de threads.
*/

#define N (10)
#define TSHARED (0)

sem_t nb_A, nb_B;

void init(void) {
    sem_init(&nb_A, TSHARED, 0);
    sem_init(&nb_B, TSHARED, 0);
}

int rdv_A(void *args) {
    (void)args;

    printf("un A est arrivé, le compter\nattendre un B\n");
    sem_post(&nb_A); // un A est arrivé, le compter
    sem_wait(&nb_B); // attendre un B
    printf("un B est arrivé\n");

    return EXIT_SUCCESS;
}

int rdv_B(void *args) {
    (void)args;

    printf("un B est arrivé, le compter\nattendre un A\n");
    sem_post(&nb_B); // un B est arrivé, le compter
    sem_wait(&nb_A); // attendre un A
    printf("un A est arrivé\n");
    
    return EXIT_SUCCESS;
}

int main(void) {
    thrd_t th_rdv_A[N], th_rdv_B[N]; // infinite loop if not the same thread number
    init();
    
    for (int i = 0; i < N; ++i)
        thrd_create(&th_rdv_A[i], rdv_A, NULL);
    
    for (int i = 0; i < N; ++i)
        thrd_create(&th_rdv_B[i], rdv_B, NULL);

    for (int i = 0; i < N; ++i)
        thrd_join(th_rdv_A[i], 0);
    
    for (int i = 0; i < N; ++i)
        thrd_join(th_rdv_B[i], 0);
    
    sem_destroy(&nb_A);
    sem_destroy(&nb_B);
    
    return EXIT_SUCCESS;
}