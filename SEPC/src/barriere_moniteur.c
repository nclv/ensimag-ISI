#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>
#include <unistd.h>

/*
Dans ce schéma de synchronisation, le but est d'organiser des groupes de N threads qui s'attendent mutuellement à une barrière. Ce schéma de synchronisation est excessivement courant, par exemple pour attendre la fin d'un calcul parallèle avant de continuer.

Une version simpliste n'est pas très difficile à faire.

int nb = 0; // état
mtx_t m;
cnd_t c;

void barriere_fausse()
{
    mtx_lock(&m);
    nb++;
    if (nb < N)
        cnd_wait(&c, &m);
    cnd_signal(&c); // réveil en cascade
    mtx_unlock(&m);
}

Mais elle est fausse, à cause du if. En effet, sur certaines architectures, des spurious wake-up peuvent survenir: les threads endormis dans la variable de condition peuvent être réveillés même si aucun thread n'a fait un signal.

Même si il n'y a pas de spurious wake-up, il n'est pas souhaitable de dépendre du flot de contrôle. Cela empêche de connaître l'état exact d'un thread, dans la logique du programme, en lisant les variables en mémoire, au débogueur ou avec des printf. Cela rend le débogage beaucoup plus complexe.

Maintenir l'état logique du système entièrement dans les variables, et pas dans le flot de contrôle, est particulièrement utile, et courant, dans les systèmes répartis ou distribuées, notamment pour faciliter la tolérance aux pannes.


L'idée est de grouper nos N threads dans une ronde (loop). Lorsque N threads sont arrivés, ils sont débloqués et la barrière passe à la ronde d'après.

Vous maintiendrez deux compteurs :

    uint64_t loop: le numéro du dernier thread arrivé dans la ronde précédente
    uint64_t count: le nombre total de threads arrivés

Chaque thread incrémente le compteur count et stocke son numéro d'arrivée dans un entier uint64_t mycount. Il s'endort tant que son numéro est strictement plus petit que loop + N. Si son numéro est égale à loop + N, il débloque tous les threads bloqués et incrémente loop de N.
*/

#define N (10)

uint64_t loop = 0;
uint64_t count = 0;
mtx_t m;
cnd_t c;

int barriere(void) {
    mtx_lock(&m);

    count++;
    uint64_t mycount = count;
    while (mycount < loop + N)
        cnd_wait(&c, &m);

    if (mycount == loop + N) {
        cnd_broadcast(&c);
        loop += N;
    }

    mtx_unlock(&m);
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
    mtx_init(&m, mtx_plain);

    for (int i = 0; i < N + 1; ++i)
        thrd_create(&threads[i], thread_routine, &ids[i]);

    for (int i = 0; i < N + 1; ++i)
        thrd_join(threads[i], 0);

    return EXIT_SUCCESS;
}