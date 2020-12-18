#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>

/*
Un groupe de N philosophes pensent et mangent des spaghettis ensembles autour d'une table ronde.

Pour manger ses spaghettis dans les règles de l'art, chaque philosophe a besoin de deux fourchettes. Une pour enrouler les spaghettis tout en s'appuyant sur l'autre.

Malheureusement, ils n'ont qu'une seule fourchette par personne. Il va donc falloir synchroniser les philosophes car pour manger, ils ont besoin de deux fourchettes.

Chaque thread philosophe doit respecter la règle suivante:
    Si un philosophe mange, alors aucun de ses deux voisins ne peut manger.

Dans cette première modélisation, nous allons modéliser uniquement les états des philosophes. Chaque philosophe son propre sémaphore privé pour s'endormir, ce qui permettra un réveil individualisé.
*/

#define N (10)

enum Etat { PENSE = 0, MANGE, AFAIM };
enum Etat etatPhilos[N] = {}; // PENSE == 0

sem_t ms; // sémaphore pour exclusion mutuelle
sem_t sprives[N];

#define THSHARED 0
void init(void) {
    sem_init(&ms, THSHARED, 1); // TSHARED == 0: sémaphore pour threads
    for (int i = 0; i < N; i++) {
        sem_init(&sprives[i], THSHARED, 0);
    }
}

/*
Teste si le philosophe i peut passer dans l'état MANGE. Pour cela la fonction vérifie qu'il est dans l'état AFAIM et que ses voisins ne mangent pas. Si elle le passe dans l'état MANGE, elle débloque aussi son sémaphore privé. Cette fonction sera utilisée trois fois (auto-test les deux tests de ces voisins quand le philosophe pose ses fourchettes).
*/
void test_mange(int mon_numero) {
    if (etatPhilos[(mon_numero + 1) % N] != MANGE &&
        etatPhilos[(mon_numero - 1 + N) % N] != MANGE && etatPhilos[mon_numero] == AFAIM) {
        etatPhilos[mon_numero] = MANGE;
        printf("Philosophe %d mange.\n", mon_numero);
        sem_post(&sprives[mon_numero]);
    }
}

// Attention, comme il est très facile de se tromper en écrivant le blocage d'un philosophe dans son sémaphore privé. Il doit intervenir après la libération de l'exclusion mutuelle, sinon il y aura interblocage. Contrairement aux moniteurs, c'est possible car les sémaphores ont une "histoire". 
void prendre_fourchettes(int mon_numero) {
    sem_wait(&ms);

    etatPhilos[mon_numero] = AFAIM;
    test_mange(mon_numero); // test/décision en exclusion mutuelle

    sem_post(&ms);
    sem_wait(&sprives[mon_numero]); // blocage plus tard
}

void poser_fourchettes(int mon_numero) {
    sem_wait(&ms);

    etatPhilos[mon_numero] = PENSE;
    printf("Philosophe %d pense.\n", mon_numero);
    test_mange((mon_numero + 1) % N);
    test_mange((mon_numero - 1 + N) % N);

    sem_post(&ms);
}

void pense(void) {
}

void mange(void) {
}

int philo(void* args) {
    int mon_numero = *(int *)args;
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