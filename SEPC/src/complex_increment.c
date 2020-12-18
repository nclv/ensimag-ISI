#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t variable = 0;

// passage de paramètres complexes
typedef struct {
    uint32_t* pvar; // adresse de la variable
    uint32_t val;   // valeur de la variable
} Thrd_args;

// incrémente la valeur de la variable
int add_to(void* args) {
    Thrd_args* t_args = (Thrd_args*)args;
    *(t_args->pvar) += t_args->val;
    return EXIT_SUCCESS;
}

// affiche la valeur de la variable
int print(void* args) {
    uint32_t* var = (uint32_t*)args;
    printf("%u\n", *var);
    return EXIT_SUCCESS;
}

int main(void) {
    add_to(&(Thrd_args){&variable, 9});
    add_to(&(Thrd_args){&variable, 11});
    print(&variable); // affiche 20
    return EXIT_SUCCESS;
}