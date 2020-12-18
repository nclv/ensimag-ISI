#include <assert.h>
#include <linux/futex.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdlib.h>
#include <sys/syscall.h>
#include <unistd.h>

/*
Lorsque l'on synchronise des threads, il y a deux activités bien distinctes à faire:

    Tester s'il faut bloquer le thread courant, ou s'il faut débloquer un thread bloqué, en regardant l'état global du système. Cela demande de lire ou d'écrire des variables en mémoire, parfois avec des fonctions atomiques, ce qui coutera quelques dizaines de cycles du processeur au maximum.
    Bloquer ou débloquer des threads, ce qui demande d'appeler le système d'exploitation, ce qui coûtera des dizaines de milliers de cycles au minimum.

L'implémentation des outils de synchronisation, comme les mutex, les variables
de condition ou les sémaphores, sépare ces deux étapes. Ils réalisent la première
en utilisant uniquement les fonctions atomiques des processeurs, sans appeler le système (peu coûteux). C'est seulement s'il faut réellement bloquer ou débloquer un thread que le système est appelé. La difficulté est qu'il faut que le test soit encore valide au moment d'un blocage. C'est le role de l'appel système futex.

La première étape est de réaliser un certain nombre d'opérations atomiques utilisant l'instruction atomique compare and exchange (en x86-64, CMPXCHG).
*/

/*
Pseudo-code similaire à l'instruction atomique CMPXCHG la fonction existe en C-11 et est directement disponible dans <stdatomic.h>.
La véritable instruction assembleur x86 est CMPXCHG. Elle est un peu plus délicate. Elle utilise le registre %eax pour stocker la valeur attendue et deux références mémoires pour la variable et la nouvelle valeur. Elle charge %eax avec la valeur lue en cas d'échec.

Si la valeur de la variable indiquée est égale à la valeur attendue, la fonction atomic_compare_and_exchange_strong écrit dans la variable la nouvelle valeur. Elle renvoie true si l'échange a été effectué, false sinon.

La version weak de la fonction peut échouer même si la variable est bien à la valeur attendue. C'est utile pour les architectures implémentant le Load Linked.
*/
bool atomic_compare_and_exchange_strong(atomic_int* variable, int* valeur_attendue, int nouvelle_valeur) {
    if (*variable == *valeur_attendue) {
        *variable = nouvelle_valeur;
        return true;
    }
    return false;
}

/*
Réalise une incrémentation atomique en utilisant la fonction atomic_compare_and_exchange_strong.

Comme l'échange peut échouer, votre fonction bouclera tant que l'opération n'est pas réussie.
*/
void atomic_increment(atomic_int* variable) {
    while (1) {
        int oldval = *variable;
        if (atomic_compare_and_exchange_strong(variable, &oldval, oldval + 1)) {
            break;
        }
    }
}

/*
Réalise une décrémentation atomique en utilisant la fonction atomic_compare_and_exchange_strong.

Comme l'échange peut échouer, votre fonction bouclera tant que l'opération n'est pas réussie.
*/
void atomic_decrement(atomic_int* variable) {
    while (1) {
        int oldval = *variable;
        if (atomic_compare_and_exchange_strong(variable, &oldval, oldval - 1)) {
            break;
        }
    }
}

/*
Réalise une décrémentation atomique, si la variable est strictement positive en
utilisant atomic_compare_and_exchange. Elle ne fait rien si la variable est
négative. Elle renvoie l’ancienne valeur de la variable dans tous les cas.
*/
int atomic_decrement_if_positive(atomic_int* variable) {
    while (1) {
        int oldval = *variable;

        if (oldval <= 0) {
            return oldval;
        }

        if (atomic_compare_and_exchange_strong(variable, &oldval, oldval - 1)) {
            return oldval;
        }
    }
    assert(0); // always fail
}

/*
Passe une variable qui vaut 0 à 1 de manière atomique.
Elle renvoie true si elle a réussi le changement, et false sinon.
*/
bool atomic_test_and_set(atomic_int* variable) {
    int oldval = *variable;
    return atomic_compare_and_exchange_strong(variable, (int*)1, 0);
}

/*
Load (Prendre une valeur en mémoire et la mettre dans un registre) et store (Prendre une valeur dans un registre est la mettre en mémoire), ont été étendues pour pouvoir servir aux synchronisations entre plusieurs threads.

On dispose d'une machine dont le jeu d'instructions comprend les opérations load linked et store conditional permettant de faire des accès atomiques sans scrutation, de manière similaire au compare_and_exchange. Ces instructions sont disponibles, par exemple dans les architectures MIPS ou RISCV.

load linked fait une lecture mémoire à une adresse donnée. Le store conditional échoue à faire son écriture à cette adresse si entre temps une écriture y a été effectuée par un autre cœur au même endroit.

L'interface en C que nous proposons pour ces instructions est, pour le load linked,
int ll(atomic_int *variable), qui retourne la valeur pointée par variable, et pour
le store conditional, bool sc(atomic_int *variable, int valeur), qui écrit valeur dans la case d'adresse variable si et seulement s'il n'y a pas eu d'accès en écriture à cette case depuis le ll, et retourne alors true, et retourne false sinon, sans modifier la case. Ainsi, le petit bout de code suivant écrira la valeur de x2

dans v si aucun autre thread n'y a fait une écriture.

int v;
...
int x = ll(&v);
if (sc(&v, x*x)) // on ne peut pas remplacer par if (sc(&v, ll(&v)*ll(&v))) car un autre processeur pourrait venir faire une écriture entre les 2 ll, alors que le sc réussirait.
    printf("Calcul de x^2 réussi !\n");
else
    printf("Caramba, encore raté !\n");
*/

int ll(atomic_int* variable);
bool sc(atomic_int* variable, int valeur);

void atomic_increment_ll(atomic_int* variable) {
    int v;

    do {
        v = ll(variable);
    } while (!sc(variable, v + 1));
}

void atomic_decrement_ll(atomic_int* variable) {
    int v;
    do {
        v = ll(variable);
    } while (!sc(variable, v - 1));
}

bool atomic_test_and_set_ll(atomic_int* variable) {
    int v;

    do {
        v = ll(variable);
        if (v)
            return false;
    } while (!sc(variable, 1));
    return true;
}

/*
On cherche à implanter un sémaphore à l'aide des fonctions codées précédemment. Nous allons utiliser le load Linked (les fonctions ll() et sc() de la section Load linked)

La sémantique des fonctions int sem_wait(sem_t *sem) et int sem_post(sem_t *sem), sera la suivante:

sem_wait(semt_t *sem)
    décrémente (verrouille) le sémaphore pointé par sem. Si la valeur du sémaphore
est strictement supérieure à zéro, alors la valeur est effectivement décrémentée et la fonction retourne immédiatement. Si la valeur est égale à zéro, alors la fonction bloque (ne retourne pas et rend la main à l'OS) jusqu'à ce que la valeur soit strictement supérieure à zéro et que la décrémentation puisse se faire ;
sem_post(sem_t *sem)
    incrémente (déverrouille) le sémaphore pointé par sem. Si la valeur du sémaphore devient en conséquence strictement supérieure à zéro, alors un thread bloqué dans un sem_wait sur ce même sémaphore est réveillée et va tenter d'acquérir le sémaphore.


Comment vérifier que la condition de blocage est encore vraie, alors que le test de cette condition a eu lieu bien avant ?


L'interface avec le système utilise l'appel système futex (man futex) à l'aide des deux fonctions suivantes :

futex_wait(int *variable, int valeur)
    il bloque le thread appelant si la valeur pointée par variable est égale à valeur.
futex_wake(int *variable, int n)
    il réveille n threads endormies sur l'adresse variable.

L'idée est que si la raison du blocage est une valeur particulière d'un entier
(par exemple 0 pour le compteur de notre sémaphore), il suffit de dire au système: "Bloque le thread, si l'entier qui est à l'adresse indiquée vaut toujours la valeur indiquée". C'est le rôle de futex_wait. L'adresse de la variable est aussi l'identifiant de la file d'attente de threads pour le système.

futex_wake sert à débloquer un nombre fixé de thread dans la file d'attente associée à la variable.

while (variable == 0) { // test: blocage si variable vaut 0
    futex_wait(& variable, 0); // blocage après le test ! "variable" peut changer entre-temps !
}

Et pour le réveil d'un seul thread:

if (variable > 0) {
    futex_wake(& variable, 1); // réveil un thread. Attention ! "variable" peut être repassée à 0! Le thread réveillé doit vérifier
}

La programmation ressemble aux moniteurs. En particulier, sur le fait de revérifier
les conditions de blocage dans un thread après son réveil (while de l'exemple précédent). Mais, attention, il y a une différence majeure. Il n'y a pas d'exclusion mutuelle entre les threads. Toutes les variables sont manipulées simultanément par plusieurs threads. Il faudra donc faire ces manipulations avec des fonctions atomiques, la plupart du temps.

Sur certaines architectures, cela peut aussi nécessiter d'ajouter, explicitement des load et des store atomiques lors de la lecture ou l'écriture de ces variables, ce que nous avons expliqué de manière brutale au compilateur avec le type atomic_int dans le struct.
*/

typedef struct {
    atomic_int semval; /* valeur courante du sémaphore */
    atomic_int asleep; /* nombre de threads endormies */
} sem_t;

// See https://connect.ed-diamond.com/GNU-Linux-Magazine/GLMF-173/Approche-detaillee-des-futex-partie-1-4
#define futex_wait(addr, val) syscall(SYS_futex, addr, FUTEX_WAIT, val, NULL)
#define futex_wake(addr, nb) syscall(SYS_futex, addr, FUTEX_WAKE, nb)

/*
La fonctionsem_initest appelée lors de création du sémaphore, dans tous les cas avantque les tâches n’y fassent appel. Ce sera donc généralement dans la fonction qui crée lestâches qui en font usage.
*/
void sem_init(sem_t* sem, int val) {
    sem->semval = val;
    sem->asleep = 0;
}

/*
Les compteurs des fonctions sem_wait et sem_post doivent être manipulés par des fonctions atomiques.
*/

int sem_wait(sem_t* sem) {
    while (1) {
        if (sem->semval > 0) {
            if (atomic_decrement_if_positive(&sem->semval)) {
                break; // décrémentation de semval réussie
            }
        }
        // semval vaut ou a valu 0
        atomic_increment_ll(&sem->asleep); // le thread se compte dans les dormeurs
        futex_wait(&sem->semval, 0); // on ne dors que si semval vaut toujours 0
        atomic_decrement_ll(&sem->asleep); // le thread décompte des dormeurs
    }
    return EXIT_SUCCESS;
}

int sem_wait_opt(sem_t* sem) {
    while (1) {
        int x = ll(&sem->semval);
        if (x > 0) {
            if (sc(&sem->semval, x - 1)) {
                break; // décrémentation de semval réussie
            } else {
                continue; // échec de la décrémentation, on relit la valeur
            }
        }
        // semval vaut ou a valu 0
        atomic_increment_ll(&sem->asleep); // incrément atomique du nombre de dormeurs
        futex_wait(&sem->semval, 0);
        atomic_decrement_ll(&sem->asleep); // décrément atomique du nombre de dormeurs
    }
    return EXIT_SUCCESS;
}

int sem_post(sem_t *sem) {
    atomic_increment_ll(&sem->semval);
    // course sur sem->semval possible ici si un sem_wait a lieu, mais alors le thread se rendormira dans la boucle while de son sem_wait
    if (sem->asleep > 0) {
        futex_wake(&sem->semval, 1);
    }
    return EXIT_SUCCESS;
}

typedef struct {
    atomic_int lock;
    atomic_int nbendormis;
} mutex_t;

void mutex_init(mutex_t *variable) {
    variable->lock = 0;
    variable->nbendormis = 0;
}

void mutex_lock(mutex_t *variable) {
    while (1) {
        if (atomic_test_and_set_ll(&variable->lock))
            break;
        atomic_increment_ll(&variable->nbendormis);
        futex_wait(&variable->lock, 1);
        atomic_decrement_ll(&variable->nbendormis);
    }
}

void mutex_unlock(mutex_t *variable) {
    variable->lock = 0;
    if (variable->nbendormis > 0) {
        futex_wait(&variable->lock, 1);
    }
}