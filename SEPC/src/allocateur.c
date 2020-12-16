#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <threads.h>

uint32_t nb_ressources = 10;
mtx_t mutex; // pour l'exclusion mutuelle des deux fonctions
cnd_t condition;

typedef struct {
    uint32_t n;
} Thrd_args;

int allouer(void *args) {
    uint32_t n = ((Thrd_args *)args)->n;
    mtx_lock(&mutex);

    // assert(nb_ressources >= n); // on ne veut pas sur-allouer
    // while (nb_ressources < n); // attente active gardant le mutex verrouillé: interblocage !
    while (nb_ressources < n) {
        cnd_wait(&condition, &mutex); // unlock sur le mutex en s'endormant et lock sur le mutex en se réveillant
        // ajouter un signal juste après le wait ne fonctionne pas
        // s'il n'y a pas assez de ressources pour les threads réveillés, par exemple deux threads qui n'ont pas assez de ressources, le premier thread qui sort du wait pcq il a été signalé va réveiller le deuxième qui n'a toujours pas assez de ressources et ça boucle à l'infini.
    }

    nb_ressources -= n;
    // ajouter un signal juste avant le unlock (réveil en cascade) ne fonctionne pas
    // s'il n'y avait pas assez de ressources pour le premier thread réveillé, il va se rendormir tout de suite et réveiller personne, même s'il y a assez de ressources pour un des threads à sa suite.
    mtx_unlock(&mutex);
    return 0;
}

int liberer(void *args) {
    uint32_t n = ((Thrd_args *)args)->n;
    mtx_lock(&mutex);
    nb_ressources += n;
    // cnd_signal(&condition); // réveil d'un seul thread: insuffisant
    // si aucune ressource et 1000 threads ils vont tous s'endormir, si un thread arrive et libère 1000 ressources un seul thread est réveillé alors qu'il reste 999 ressources (et 999 threads endormis)
    cnd_broadcast(&condition); // réveille tous les threads
    mtx_unlock(&mutex);
    return 0;
}

int main(void) {
    thrd_t th1, th2;
    mtx_init(&mutex, mtx_plain);
    thrd_create(&th1, allouer, &(Thrd_args) {10});
    thrd_create(&th2, liberer, &(Thrd_args) {5});
    thrd_join(th1, 0);
    thrd_join(th2, 0);
    printf("%u \n", nb_ressources);
}