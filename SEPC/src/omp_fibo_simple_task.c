#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint64_t fibo_seq(uint32_t n) {
    if (n < 2)
        return n;

    return fibo_seq(n - 1) + fibo_seq(n - 2);
}

uint64_t fibo_par(uint32_t n) {
    if (n < 2)
        return n;

    uint64_t r1;
    uint64_t r2;
#pragma omp task shared(r1) firstprivate(n) default(none) // indiquer que vos temporaires sont partagées entre la tâche créée et la tâche courante et créer automatiquement un temporaire pour n en copiant la valeur initiale lors de la création de la tâche.
    r1 = fibo_par(n - 1);
#pragma omp task shared(r2) firstprivate(n) default(none)
    r2 = fibo_par(n - 2);
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

#pragma omp task shared(res) default(none)
            res = fibo_par(7);

#pragma omp taskwait
            printf("%lu\n", res); // ajustez pour durer 8s
        }
    }
    return EXIT_SUCCESS;
}
