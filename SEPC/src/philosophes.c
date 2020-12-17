#include <stdio.h>
#include <threads.h>

/*
Un groupe de N philosophes pensent et mangent des spaghettis ensembles autour d'une table ronde.

Pour manger ses spaghettis dans les règles de l'art, chaque philosophe a besoin de deux fourchettes. Une pour enrouler les spaghettis tout en s'appuyant sur l'autre.

Malheureusement, ils n'ont qu'une seule fourchette par personne. Il va donc falloir synchroniser les philosophes car pour manger, ils ont besoin de deux fourchettes.

Chaque thread philosophe doit respecter la règle suivante:
    Si un philosophe mange, alors aucun de ses deux voisins ne peut manger.

Dans cette première modélisation, nous allons modéliser uniquement les états des philosophes. Chaque philosophe aura sa propre variable de condition pour s'endormir, ce qui permettra un réveil individualisé.
*/

#define N (10)

enum Etat {
    PENSE = 0,
    MANGE = 1,
    AFAIM = 2
}; // première variante avec AFAIM qui permet d'éviter de faire les cnd_signal pour rien
enum Etat etatPhilos[N] = {}; // PENSE == 0

mtx_t m;
cnd_t files_privees[N]; // une autre variante possible consiste à n'utiliser qu'une seule variable de condition et à faire systématiquement un broadcast en posant les fourchettes.

void prendre_fourchettes(int mon_numero) {
    mtx_lock(&m);

    // (0 - 1 + N) % N == N - 1 plutôt que (0 - 1) % N == -1 pour rester avec des entiers positifs
    while (etatPhilos[(mon_numero + 1) % N] == MANGE ||
           etatPhilos[(mon_numero - 1 + N) % N] == MANGE) {
        etatPhilos[mon_numero] = AFAIM;
        cnd_wait(&files_privees[mon_numero], &m);
    }
    etatPhilos[mon_numero] = MANGE;
    printf("Philosophe %d mange.\n", mon_numero);

    mtx_unlock(&m);
}

void poser_fourchettes(int mon_numero) {
    mtx_lock(&m);

    etatPhilos[mon_numero] = PENSE;
    printf("Philosophe %d pense.\n", mon_numero);
    cnd_signal(&files_privees[(mon_numero + 1) % N]);
    cnd_signal(&files_privees[(mon_numero - 1 + N) % N]);

    mtx_unlock(&m);
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
    return 0;
}

int main(void) {
    int numeros[N] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    thrd_t th_philosophe[N];
    mtx_init(&m, mtx_plain);

    for (int i = 0; i < N; ++i)
        thrd_create(&th_philosophe[i], philo, &numeros[i]);

    for (int i = 0; i < N; ++i)
        thrd_join(th_philosophe[i], 0);

    return 0;
}