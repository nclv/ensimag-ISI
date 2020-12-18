#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <semaphore.h>
#include <threads.h>

/*
Deux types de threads veulent accéder à une ressource partagée, par exemple une base de données ou un fichier. Les lecteurs veulent accéder à la ressource pour la consulter alors que les rédacteurs veulent la modifier.

Les threads doivent respecter les règles suivantes :

    il ne peut y avoir au plus qu'un seul thread rédacteur à la fois
    aucun thread lecteur ne peut consulter la ressource pendant qu'un rédacteur la modifie
    plusieurs lectures sont possibles en même temps

Faire un accès en exclusion mutuelle à la base de donnée est facile. Il suffit d'un seul sémaphore sem_t acces.

Ce sémaphore doit être pris par le premier lecteur à entrer et être relaché par le dernier lecteur à sortir. Pour cela il va falloir les compter, int nb_lecteur; et pour que le compte se passe bien entre plusieur threads, il va falloir manipuler ce compteur en exclusion mutuelle sem_t ms.

Enfin, pour éviter les famines, nous utiliserons un sas: un sémaphore avec un seul crédit pour garder les deux entrées. La file d'attente du sémaphore sera supposée FIFO.
*/

int nb_lect = 0;
sem_t acces;
sem_t ms;
sem_t sas;

#define TSHARED 0
void init(void) {
    sem_init(&ms, TSHARED, 1);
    sem_init(&acces, TSHARED, 1);
    sem_init(&sas, TSHARED, 1);
}

void debut_lire(void) {
    sem_wait(&sas);
    sem_wait(&ms);
    
    nb_lect++;
    if (nb_lect == 1)
        sem_wait(&acces);
    // ne relache pas le mutex (fonctionnalite, ce n'est pas un bug !)
    
    sem_post(&ms);
    sem_post(&sas);
}

void fin_lire(void) {
    sem_wait(&ms);

    nb_lect--;
    if (nb_lect == 0)
        sem_post(&acces);
    
    sem_post(&ms);
}

void debut_redac(void) {
    sem_wait(&sas);
    sem_wait(&acces);
    sem_post(&sas);
}

void fin_redac(void) {
    sem_post(&acces);
}


#define N (10) // 10 lecteurs et 10 rédacteurs
typedef struct ressource_s {
    uint32_t value;
} ressource_t;
static ressource_t rsrc = {100}; // ressource partagee initialisée

int lecteur(void* args) {
    (void)args;
    debut_lire();

    // opérations lisant rsrc
    printf("\nLecteur:");
    printf("Lecture: %u\n", rsrc.value);

    fin_lire();
    return EXIT_SUCCESS;
}

int redacteur(void* args) {
    ressource_t* res = (ressource_t*)args;
    debut_redac();

    // opérations lisant et modifiant rsrc
    printf("\nRédacteur:");
    printf("Lecture: %u\n", rsrc.value);
    rsrc.value = res->value;
    printf("Ecriture: %u\n", rsrc.value);

    fin_redac();
    return EXIT_SUCCESS;
}

int main(void) {
    ressource_t ressources[N] = {{0}, {1}, {2}, {3}, {4},
                                 {5}, {6}, {7}, {8}, {9}};
    thrd_t th_lecteur[N / 2], th_redacteur[N];
    init();

    for (int i = 0; i < N; ++i)
        thrd_create(&th_redacteur[i], redacteur, &ressources[i]);

    for (int i = 0; i < N / 2; ++i)
        thrd_create(&th_lecteur[i], lecteur, NULL);

    for (int i = 0; i < N; ++i)
        thrd_join(th_redacteur[i], 0);
    
    for (int i = 0; i < N / 2; ++i)
        thrd_join(th_lecteur[i], 0);

    return EXIT_SUCCESS;
}