#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/*
La création d'une tâche est beaucoup plus coûteuse qu'une addition.
Pour limiter ce surcoût, il faut de rebasculer vers l'algorithme séquentiel lorsqu'il y a assez de tâches.
*/

uint64_t fibo_seq(uint32_t n) {
    if (n < 2)
        return n;

    return fibo_seq(n - 1) + fibo_seq(n - 2);
}

uint64_t fibo_par(uint32_t n, uint32_t prof) {
    if (prof <= 0)
        return fibo_seq(n);

    if (n < 2)
        return n;

    uint64_t r1;
    uint64_t r2;
#pragma omp task shared(r1) firstprivate(n, prof) default(none)
    r1 = fibo_par(n - 1, prof - 1);
#pragma omp task shared(r2) firstprivate(n, prof) default(none)
    r2 = fibo_par(n - 2, prof - 1);
#pragma omp taskwait
    return r1 + r2;
}

int main(int argc, char** argv) {
    (void)argc;
    (void)argv;
#pragma omp parallel
    {
#pragma omp single
        {
            uint64_t res;

#pragma omp task shared(res) default(none) // lastprivate(res)
            res = fibo_par(47, 4);

#pragma omp taskwait
            printf("%lu\n", res); // ajustez pour durer 8s
        }
    }
    return EXIT_SUCCESS;
}