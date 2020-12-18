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

L'interblocage vient du cycle de dépendances entre les philosophes. Une façon d'empêcher la création de ce cycle est de garantir que tous les philosophes prennent les fourchettes dans le même ordre global. Dans le contre-exemple, tous les philosophes prennent la fourchette de plus petit numéro d'abord (i), puis celle de plus grand numéro ensuite (i + 1) sauf le philopshe N - 1 qui commence par prendre la fourchette N - 1 puis la fourchette 0.
*/

#define N (10)

enum Etat { PENSE = 0, MANGE};
enum Etat etatPhilos[N] = {}; // PENSE == 0

sem_t fourchettes[N];

#define THSHARED 0
void init(void) {
    for (int i = 0; i < N; i++) {
        sem_init(&fourchettes[i], THSHARED, 1);
    }
}

void prendre_fourchettes(int i) {
    etatPhilos[i] = MANGE;
    printf("Philosophe %d mange.\n", i);
    if (i == N - 1) {
        sem_wait(&fourchettes[(i + 1) % N]); // (i + 1) % N == (N - 1 + 1) % N == 0
        sem_wait(&fourchettes[i]);
    } else {
        sem_wait(&fourchettes[i]);
        sem_wait(&fourchettes[(i + 1) % N]);
    }
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