#include <omp.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint64_t fibo_seq(uint32_t n) {
    if (n < 2)
        return n;

    return fibo_seq(n - 1) + fibo_seq(n - 2);
}

uint64_t somme(uint64_t r1, uint64_t r2) {
    return r1 + r2;
}

uint64_t fibo_par(uint32_t n, int prof) {
    if (prof <= 0)
        return fibo_seq(n);

    // printf("%d from %d\n", n, omp_get_thread_num());
    if (n < 2)
        return n;

    uint64_t res1;
    uint64_t res2;
    uint64_t res;

#pragma omp task depend(out                           \
                        : res1) firstprivate(n, prof) \
    shared(res1) default(none) final((prof - 1) == 0)
    res1 = fibo_par(n - 1, prof - 1);

#pragma omp task depend(out                           \
                        : res2) firstprivate(n, prof) \
    shared(res2) default(none) final((prof - 1) == 0)
    res2 = fibo_par(n - 2, prof - 1);

#pragma omp task shared(res, res1, res2) depend(in \
                                                : res1, res2) final(true) default(none)
    res = somme(res1, res2);

#pragma omp taskwait
    return res;
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
            val = fibo_par(47, 4);
        }
    }
    printf("%lu\n", val); // environ 8s sur mon laptop
    return EXIT_SUCCESS;
}