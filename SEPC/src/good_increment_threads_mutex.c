#include <stdio.h>
#include <threads.h> // C11, need to link -pthread

static int compteur = 0;
mtx_t mutex;

void incremente(void) {
    mtx_lock(&mutex);   // un seul thread à la fois
    compteur++;         // section critique
    mtx_unlock(&mutex); // on passe la main au prochain thread
}

int loop(void* arg) {
    void (*f)(void) = (void (*)(void))arg;
    for (int i = 0; i < 1000000; ++i) {
        f();
    }
    return 0;
}

int main(void) {
    thrd_t th1, th2;
    mtx_init(&mutex, mtx_plain);
    thrd_create(&th1, loop, (void*)incremente);
    thrd_create(&th2, loop, (void*)incremente);
    thrd_join(th1, 0);
    thrd_join(th2, 0);
    printf("compteur incrémenté: %d/2000000\n", compteur);
}