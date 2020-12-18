#include <semaphore.h>
#include <stdio.h>
#include <threads.h>

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
    sem_post(&nb_A); // un A est arrivé, le compter
    printf("un A est arrivé, le compter\nprendre un B\n");
    sem_wait(&nb_B); // prendre un B
    return 0;
}

int rdv_B(void *args) {
    (void)args;
    sem_post(&nb_B); // un B est arrivé, le compter
    printf("un B est arrivé, le compter\nprendre un A\n");
    sem_wait(&nb_A); // prendre un A
    return 0;
}

int main(void) {
    thrd_t th_rdv_A[N], th_rdv_B[N];
    init();
    
    for (int i = 0; i < N; ++i)
        thrd_create(&th_rdv_A[i], rdv_A, NULL);

    for (int i = 0; i < N / 2; ++i)
        thrd_create(&th_rdv_B[i], rdv_B, NULL);

    for (int i = 0; i < N; ++i)
        thrd_join(th_rdv_A[i], 0);
    
    for (int i = 0; i < N / 2; ++i)
        thrd_join(th_rdv_B[i], 0);
    
    return 0;
}