#include <semaphore.h>
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

#define N (5) // état

typedef struct message_s {
    uint32_t message;
} message_t;

static message_t* tampon[N]; // état
static message_t* return_mess;

int ilec = 0;
int iecr = 0;
sem_t ms; // mutex semaphore
sem_t cvides;
sem_t cpleines;

#define TSHARED 0
void init(void) {
    sem_init(&ms, TSHARED, 1);
    sem_init(&cvides, TSHARED, N);
    sem_init(&cpleines, TSHARED, 0);
}

int deposer(void* args) {
    message_t* mess = (message_t*)args;

    printf("\nAttente d'une place libre");
    sem_wait(&cvides); // wait/sleep when there are no empty slots
    sem_wait(&ms);

    tampon[iecr] = mess;
    iecr = (iecr + 1) % N;

    printf("\nMessage déposé\n");
    printf("Tampon: ");
    for (int i = 0; i < N; ++i) {
        if (tampon[i] != NULL)
            printf("%u, ", tampon[i]->message);
    }

    printf("\nIl y a une place remplie en plus\n");
    sem_post(&ms);
    sem_post(&cpleines); // Signal/wake to consumer that buffer has some data and they can consume now

    return EXIT_SUCCESS;
}

int retirer(void* args) {
    (void)args;

    printf("\nAttente d'une place remplie");
    sem_wait(&cpleines); // wait/sleep when there are no full slots
    sem_wait(&ms);

    return_mess = tampon[ilec];
    tampon[ilec] = NULL;
    ilec = (ilec + 1) % N;

    printf("\nMessage retiré: %u\n", return_mess->message);
    printf("Tampon: ");
    for (int i = 0; i < N; ++i) {
        if (tampon[i] != NULL)
            printf("%u, ", tampon[i]->message);
    }

    printf("\nIl y a une place vide en plus\n");
    sem_post(&ms);
    sem_post(&cvides); // Signal/wake the producer that buffer slots are emptied and they can produce more

    return EXIT_SUCCESS;
}

int main(void) {
    message_t messages[N] = {{0}, {1}, {2}, {3}, {4}};
    thrd_t th_deposer[N], th_retirer[N / 2];
    init();

    for (int i = 0; i < N / 2; ++i)
        thrd_create(&th_retirer[i], retirer, NULL);

    for (int i = 0; i < N; ++i)
        thrd_create(&th_deposer[i], deposer, &messages[i]);

    for (int i = 0; i < N; ++i)
        thrd_join(th_deposer[i], 0);

    for (int i = 0; i < N / 2; ++i)
        thrd_join(th_retirer[i], 0);

    sem_destroy(&ms);
    sem_destroy(&cvides);
    sem_destroy(&cpleines);

    return EXIT_SUCCESS;
}