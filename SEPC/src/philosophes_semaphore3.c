#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>

/*
Une autre possibilité de modélisation est d'utiliser un sémaphore par fourchette:

sem_t fourchettes[N];

Mais la prise simpliste de ces sémaphores ne fonctionne pas:

void prendre_fourchette(int i) {
    sem_wait(&fourchettes[i]);
    sem_wait(&fourchettes[(i + 1) % N]);
}

void poser_fourchette(int i) {
    sem_post(&fourchettes[i]);
    sem_post(&fourchettes[(i + 1) % N]);
}

En effet, si tous les philosophes réussissent à prendre la fourchette à leur droite (la fourchette numéro i), il ne reste aucune fourchette sur la table. Il y a donc interblocage.

Dans ce problème, le cycle de dépendance de l'interblocage est toujours de longueur N. Une autre façon d'empêcher l'apparition de l'interblocage est de ne laisser que N - 1 philosophes essayer de prendre les fourchettes, et donc rend impossible la création d'un cycle de longueur N.
*/

#define N (10)

enum Etat { PENSE = 0, MANGE };
enum Etat etatPhilos[N] = {}; // PENSE == 0

sem_t table;
sem_t fourchettes[N];

#define THSHARED 0
void init(void) {
    sem_init(&table, THSHARED, N - 1);
    for (int i = 0; i < N; i++) {
        sem_init(&fourchettes[i], THSHARED, 1);
    }
}

void prendre_fourchettes(int i) {
    sem_wait(&table);

    etatPhilos[i] = MANGE;
    printf("Philosophe %d mange.\n", i);
    sem_wait(&fourchettes[i]);
    sem_wait(&fourchettes[(i + 1) % N]);

    sem_post(&table);
}

void poser_fourchettes(int i) {
    // l'ordre de dépose des fourchettes n'a aucune importance
    etatPhilos[i] = PENSE;
    printf("Philosophe %d pense.\n", i);
    sem_post(&fourchettes[i]);
    sem_post(&fourchettes[(i + 1) % N]);
}

void pense(void) {
}

void mange(void) {
}

int philo(void* args) {
    int mon_numero = *(int*)args;
    int k = 0;
    while (k < 5) { // plutôt que while (1)
        pense();
        prendre_fourchettes(mon_numero);
        mange();
        poser_fourchettes(mon_numero);
        ++k;
    }
    return EXIT_SUCCESS;
}

int main(void) {
    int numeros[N] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    thrd_t th_philosophe[N];
    init();

    for (int i = 0; i < N; ++i)
        thrd_create(&th_philosophe[i], philo, &numeros[i]);

    for (int i = 0; i < N; ++i)
        thrd_join(th_philosophe[i], 0);

    return EXIT_SUCCESS;
}