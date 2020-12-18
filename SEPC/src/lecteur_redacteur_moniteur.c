#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>

/*
Deux types de threads veulent accéder à une ressource partagée, par exemple une base de données ou un fichier. Les lecteurs veulent accéder à la ressource pour la consulter alors que les rédacteurs veulent la modifier.

Les threads doivent respecter les règles suivantes :

    il ne peut y avoir au plus qu'un seul thread rédacteur à la fois
    aucun thread lecteur ne peut consulter la ressource pendant qu'un rédacteur la modifie
    plusieurs lectures sont possibles en même temps

bool redac; si il y a un rédacteur dans la base
int nb_lect; le nombre de lecteurs dans la base
int att_nb__redac; le nombre de rédacteurs en attente dans debut_redac()
int att_nb__lect; le nombre de lecteurs en attente dans debut_lect()

La priorité sera donné aux rédacteurs. Cela change l'attente dans debut_lect et le réveil dans fin_redac()
*/

mtx_t m;
int att_nb_lect = 0; // lect. en attente
int nb_lect = 0;
int att_nb_redac = 0; // redac. en attente
bool redac = false;
cnd_t flect;
cnd_t fredac;

/*
Le comptage des threads en attente est soit dans le while (comme dans la solution), ou autour du while. Cela n'a que peu d'incidence sur la performance du code ici. Néanmoins, une bonne raison pour les mettre dans le while est le fait que ces compteurs ne concernent que le 'slow path', celui où le programme est obligé d'appeler le système (le wait), ce qui va coûter cher de toute façon.
*/
void debut_lire(void) {
    mtx_lock(&m);

    while (redac || att_nb_redac != 0) {
        att_nb_lect++;
        cnd_wait(&flect, &m);
        att_nb_lect--;
    }
    nb_lect++;

    mtx_unlock(&m);
}

void debut_redac(void) {
    mtx_lock(&m);

    while (nb_lect > 0 || redac) {
        att_nb_redac++;
        cnd_wait(&fredac, &m);
        att_nb_redac--;
    }
    redac = true;

    mtx_unlock(&m);
}

void fin_lire(void) {
    mtx_lock(&m);

    nb_lect--;
    if (nb_lect == 0 && att_nb_redac != 0)
        cnd_signal(&fredac);

    mtx_unlock(&m);
}

void fin_redac(void) {
    mtx_lock(&m);

    redac = false;
    if (att_nb_redac > 0) {
        cnd_signal(&fredac);
    } else if (att_nb_lect > 0) {
        cnd_broadcast(&flect);
    }

    mtx_unlock(&m);
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

/*
Pourquoi ne pas garder le lock pendant toute la durée de la rédaction?

Rien ne peut avoir lieu en même temps qu'un rédacteur et donc garder le lock tant qu'il travaille ne changerait rien. 
Néanmoins, pour pouvoir assurer la priorité aux rédacteurs, il est nécessaire que ces derniers puissent s'annoncer, et se bloquer sur une condition quand ils arrivent alors qu'un rédacteur est en train de travailler sur la ressource partagée. 
En effet, si le rédacteur garde le lock, alors les rédacteurs ne se bloquent  plus sur la condition via le wait mais sur le lock et nous n'avons aucune garantie que ce lock sera donné en priorité aux lecteurs lorsque le rédacteur aura fini. Autrement dit, le lock peut être donné à un rédacteur également arrivé pendant la rédaction.
*/
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
    mtx_init(&m, mtx_plain);

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