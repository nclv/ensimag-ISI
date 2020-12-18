#include <semaphore.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>
#include <unistd.h>

/*
Dans ce schéma de synchronisation, le but est d'organiser des groupes de N threads qui s'attendent mutuellement à une barrière. Ce schéma de synchronisation est excessivement courant, par exemple pour attendre la fin d'un calcul parallèle avant de continuer.

Une version simpliste pourrait être la suivante:

uint64_t count = 0;
sem_t ms = 1;
sem_t barrier = 0;

#define TSHARED 0
void init(void) {
    sem_init(&ms, TSHARED, 1);
    sem_init(&barrier, TSHARED, 0);
}

void barriere(void) {
    sem_wait(&ms);
    count++;
    sem_post(&ms);

    if (count == N)
        sem_post(&barrier); // le dernier reveil un des threads

    sem_wait(&barrier); // attente
    sem_post(&barrier); // reveil en cascade
 }

Mais cette version a des grosses limitations:

    elle n'est utilisable qu'une seule fois;
    il ne faut pas plus de N threads appelant la fonction ! Sinon le N + 1 pourrait incrémenter count avant que le Nième n'ai fini le test de son if, provoquant un interblocage. Ce point est corrigeable en terminant le mutex après la fin du if.



Les sémaphores permettent de facilement synchroniser en comptant. Dans la solution proposée, il faudra

    compter et synchroniser les threads arrivés pour n'en laisser que N entrer (sem_t sas);
    les N-1 premiers doivent se bloquer (sem_t barrier);
    le N-ième doit:
        les débloquer;
        le N-ième doit compter et se synchroniser avec les threads partant pour être sur que la barrière est à nouveau vide (sem_t out);
        puis permettre aux N suivant d'entrer en incrémentant sas de N;

Pour arbitrer, il faut identifier le dernier threads du groupe. uint64_t count: compte le nombre total de threads arrivés. L'incrémentation de count et la sauvegarde de sa valeur pour le thread courant (unint64_t mycount) doivent être faite en exclusion mutuelle (sem_t ms).

Pour un thread qui n'est pas le dernier du groupe:

    il rentre dans le sas;
    il prend son numéro en exclusion mutuelle;
    il attend à la barrière;
    il previent le dernier thread qu'il est parti.

Pour le thread qui est le dernier du groupe:

    il rentre dans le sas;
    il prend son numéro en exclusion mutuelle;
    il débloque tous les autres threads bloqués à la barrière;
    il attend que tous les autres soient partis;
    il redonne N place libre au sas.

Pour incrémenter un sémaphore de N valeurs, il suffit de faire une boucle:

sem_t sem;
for (int i=0; i < N; ++i) {  // incrémente sem de N
    sem_post(&sem);
}
*/

#define N (10)

uint64_t count = 0;
sem_t sas;
sem_t ms;
sem_t barrier;
sem_t out;

#define TSHARED 0
void init(void) {
    sem_init(&ms, TSHARED, 1);
    sem_init(&sas, TSHARED, N);
    sem_init(&barrier, TSHARED, 0);
    sem_init(&out, TSHARED, 0);
}

/*
Vous noterez que dans cette implantation, les compteurs sont monotones et que l'on connaît pour chaque thread dans la barrière son ordre d'arrivée, y compris pour les threads des rondes précédentes qui n'ont pas encore réussis à attraper le mutex pour sortir du sem_wait et partir.
*/
int barriere(void) {
    sem_wait(&sas); // only N threads will pass

    sem_wait(&ms);
    count++;
    uint64_t mycount = count; // copy count value !
    sem_post(&ms);

    if (mycount % N != 0) {             // not the last of the group
        sem_wait(&barrier);             // wait here
        sem_post(&out);                 // count as leaving
    } else {                            // I am the last of the group
        for (int i = 0; i < N - 1; i++) // release the N-1 others
            sem_post(&barrier);
        for (int i = 0; i < N - 1; i++) // wait the N-1 others all leave
            sem_wait(&out);
        for (int i = 0; i < N; i++) // Let the next N enter
            sem_post(&sas);
    }
    return EXIT_SUCCESS;
}

int thread_routine(void* args) {
    int thread_num = *(int*)args;
    printf("-- Thread %d Start -- \n", thread_num);
    int ret;

    for (int i = 0; i <= (thread_num * 2); ++i) {
        printf(" Thread-%d, Before barrier-%d\n", thread_num, i);
        sleep(1);
    }
    printf(" Thread-%d finish it's work & wait for other thread\n", thread_num);

    ret = barriere();
    printf(" Thread-%d Resume. barrier_wait return:%d\n", thread_num, ret);
    printf("-- Thread %d End -- \n", thread_num);
    return EXIT_SUCCESS;
}

int main(void) {
    int ids[N + 1] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
    thrd_t threads[N + 1];
    init();

    for (int i = 0; i < N + 1; ++i)
        thrd_create(&threads[i], thread_routine, &ids[i]);

    for (int i = 0; i < N + 1; ++i)
        thrd_join(threads[i], 0);

    return EXIT_SUCCESS;
}
