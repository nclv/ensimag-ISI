#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>

uint32_t variable = 0;
mtx_t m;

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
    mtx_unlock(&m);
    return EXIT_SUCCESS;
}

// affiche la valeur de la variable
int print(void* args) {
    mtx_lock(&m);
    uint32_t* var = (uint32_t*)args;
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