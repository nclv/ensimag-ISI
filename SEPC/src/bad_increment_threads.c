#include <stdio.h>
#include <threads.h> // C11, need to link -pthread

volatile int compteur = 0;

void incremente(void) {
    compteur++; // section critique
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
    thrd_create(&th1, loop, (void*)incremente);
    thrd_create(&th2, loop, (void*)incremente);
    thrd_join(th1, 0);
    thrd_join(th2, 0);
    printf("compteur incrémenté: %d/2000000\n", compteur);
}