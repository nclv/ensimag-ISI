#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>

uint32_t variable = 0;
mtx_t m;
int nb_fini = 0; // compteur du nombre de threads ayant fini
cnd_t c;         // file d'attente du thread d'affichage

// passage de paramètres complexes
typedef struct {
    uint32_t* pvar; // adresse de la variable
    uint32_t val;   // valeur de la variable
} Thrd_args;

// incrémente la valeur de la variable
int add_to(void* args) {
    mtx_lock(&m);
    Thrd_args* t_args = (Thrd_args*)args;
    *(t_args->pvar) += t_args->val;

    nb_fini++;          // se compter
    if (nb_fini == 2)   // si je suis le dernier
        cnd_signal(&c); // réveiller le thread d'affichage

    mtx_unlock(&m);
    return EXIT_SUCCESS;
}

// affiche la valeur de la variable
int print(void* args) {
    mtx_lock(&m);
    uint32_t* var = (uint32_t*)args;

    // un wait est toujours dans un while
    while (nb_fini < 2)   // si les threads de calculs n'ont pas finis
        cnd_wait(&c, &m); // attendre leur signal

    printf("%u\n", *var);
    mtx_unlock(&m);
    return EXIT_SUCCESS;
}

int main(void) {
    Thrd_args T_args[2] = {{&variable, 9}, {&variable, 11}};
    // T_args doit être valide jusqu'au join (attention au scope)
    thrd_t th_add[2], th_print;

    for (int i = 0; i < 2; ++i) {
        thrd_create(&th_add[i], add_to, &T_args[i]);
    }
    thrd_create(&th_print, print, &variable);

    for (int i = 0; i < 2; ++i) {
        thrd_join(th_add[i], NULL);
    }
    thrd_join(th_print, NULL); // afficher peut s'exécuter avant l'incrémentation

    // ce programme n'affiche pas toujours 20, une solution est de déplacer le create de la fonction print après la boucle join
    return EXIT_SUCCESS;
}