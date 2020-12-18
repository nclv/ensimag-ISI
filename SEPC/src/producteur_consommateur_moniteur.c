#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>

/*
Deux types de threads échangent des messages par le biais d'un tampon. Les producteurs écrivent des messages dans le tampon alors que les consommateurs les suppriment. Les règles sont les suivantes:

    un seul thread modifie le tampon à la fois
    le tampon est de taille bornée
    si il n'y a pas de messages dans le tampon, les consommateurs se mettent en attente
    si le tampon est plein, les producteurs se mettent en attente

Le tampon est un simple tableau de taille N et du type des message à écrire dedans.
*/

#define N (10) // état

typedef struct message_s {
    uint32_t message;
} message_t;

static message_t* tampon[N]; // état
static message_t* return_mess;

mtx_t m;
int nb_cases_vides = N;
int ilec = 0;
int iecr = 0;
cnd_t file_prod;
cnd_t file_conso;

int deposer(void* args) {
    message_t* mess = (message_t*)args;
    mtx_lock(&m);

    while (nb_cases_vides == 0)
        cnd_wait(&file_prod, &m);

    tampon[iecr] = mess;
    iecr = (iecr + 1) % N;
    nb_cases_vides--;

    printf("\nMessage déposé\n");
    printf("Tampon: ");
    for (int i = 0; i < N; ++i) {
        if (tampon[i] != NULL)
            printf("%u, ", tampon[i]->message);
    }

    cnd_signal(&file_conso);
    mtx_unlock(&m);
    return EXIT_SUCCESS;
}

int retirer(void* args) {
    (void)args;
    mtx_lock(&m);

    while (nb_cases_vides == N)
        cnd_wait(&file_conso, &m);

    return_mess = tampon[ilec];
    tampon[ilec] = NULL;
    ilec = (ilec + 1) % N;
    nb_cases_vides++;

    printf("\nMessage retiré: %u\n", return_mess->message);
    printf("Tampon: ");
    for (int i = 0; i < N; ++i) {
        if (tampon[i] != NULL)
            printf("%u, ", tampon[i]->message);
    }
    printf("\n");

    cnd_signal(&file_prod);
    mtx_unlock(&m);
    return EXIT_SUCCESS;
}

int main(void) {
    message_t messages[N] = {{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}, {9}};
    thrd_t th_deposer[N], th_retirer[N / 2];
    mtx_init(&m, mtx_plain);

    for (int i = 0; i < N; ++i)
        thrd_create(&th_deposer[i], deposer, &messages[i]);

    for (int i = 0; i < N / 2; ++i)
        thrd_create(&th_retirer[i], retirer, NULL);

    for (int i = 0; i < N; ++i)
        thrd_join(th_deposer[i], 0);

    for (int i = 0; i < N / 2; ++i)
        thrd_join(th_retirer[i], 0);

    return EXIT_SUCCESS;
}