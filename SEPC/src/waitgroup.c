#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>
#include <unistd.h>

/*
Dans ce schéma de synchronisation, un groupe de threads, les waiters, attend la fin des calculs d'un nombre N variable de DONE, faits par d'autres threads, les workers. Ce schéma de synchronisation est utilisé en Go, par exemple.

Chaque WaitGroup est à usage unique. Il est possible d'augmenter, ou diminuer N avec la fonction add(), tant qu'il n'est pas tombé à 0. Chaque worker appelle la fonction done() quand il a fini. Cette fonction décrémente N de 1. Chaque waiter attends, bloqué dans la fonction wait() tant que tous les worker n'ont pas indiqué avoir fini.
*/

#define N (10)

typedef struct waitgroup {
    int n;
    bool fini;
    mtx_t m;
    cnd_t cg;
} WaitGroup;

void init(WaitGroup* g) {
    g->fini = false;
    g->n = 0;
    mtx_init(&g->m, mtx_plain);
    cnd_init(&g->cg);
}

void test_fin_attente(WaitGroup* g) {
    assert(g->n >= 0);

    if (g->n == 0) {
        g->fini = true;
        cnd_broadcast(&g->cg);
    }
}

void add(WaitGroup* g, int n) {
    mtx_lock(&g->m);
    assert(!g->fini);

    g->n += n;
    test_fin_attente(g);

    mtx_unlock(&g->m);
}

void done(WaitGroup* g) {
    mtx_lock(&g->m);
    assert(!g->fini);

    g->n--;
    test_fin_attente(g);

    mtx_unlock(&g->m);
}

void wait(WaitGroup* g) {
    mtx_lock(&g->m);

    test_fin_attente(g); // si N reste à 0
    while (!g->fini) {
        cnd_wait(&g->cg, &g->m);
    }

    mtx_unlock(&g->m);
}

WaitGroup* g = NULL;

int thread_routine(void* args) {
    int thread_num = *(int*)args;
    printf("-- Thread %d Start -- \n", thread_num);

    for (int i = 0; i <= (thread_num * 2); ++i) {
        printf(" Thread-%d, Before barrier-%d\n", thread_num, i);
        sleep(1);
    }
    printf(" Thread-%d finish it's work & wait for other thread\n", thread_num);

    printf(" Thread-%d Resume.\n", thread_num);
    printf("-- Thread %d End -- \n", thread_num);
    done(g);
    return EXIT_SUCCESS;
}

int main(void) {
    int ids[N + 1] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
    thrd_t threads[N + 1];

    g = malloc(sizeof *g);
    if (g == NULL) return 1;
    init(g);

    for (int i = 0; i < N + 1; ++i) {
        add(g, 1);
        thrd_create(&threads[i], thread_routine, &ids[i]);
    }
    wait(g);

    for (int i = 0; i < N + 1; ++i)
        thrd_join(threads[i], 0);

    if (g != NULL) free(g);

    return EXIT_SUCCESS;
}