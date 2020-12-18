#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint64_t fibo_seq(uint32_t n) {
    if (n < 2)
        return n;

    return fibo_seq(n - 1) + fibo_seq(n - 2);
}

void somme(uint64_t* r1, uint64_t* r2, uint64_t* res) {
    *res = *r1 + *r2;
    free(r1);
    free(r2);
}

void fibo_par(uint32_t n, uint64_t* res, int prof) {
    if (prof <= 0) {
        *res = fibo_seq(n);
        return;
    }

    // printf("%d from %d\n", n, omp_get_thread_num());
    if (n < 2) {
        *res = n;
        return;
    }

    uint64_t* res1 = malloc(sizeof(uint64_t));
    uint64_t* res2 = malloc(sizeof(uint64_t));

#pragma omp task depend(out : res1)
    fibo_par(n - 1, res1, prof - 1);

#pragma omp task depend(out : res2)
    fibo_par(n - 2, res2, prof - 1);

#pragma omp task shared(res) depend(in : res1, res2)
    somme(res1, res2, res);

#pragma omp taskwait
}

int main(int argc, char** argv) {
    (void)argc;
    (void)argv;
    uint64_t val;
#pragma omp parallel
    {
#pragma omp single
        {
#pragma omp task shared(val)
            fibo_par(47, &val, 4);
        }
    }
    printf("%lu\n", val); // environ 8s sur mon laptop
    return EXIT_SUCCESS;
}