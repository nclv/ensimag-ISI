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

    return fibo_par(n - 1) + fibo_par(n - 2);
}

int main(int argc, char** argv) {
    (void)argc;
    (void)argv;
#pragma omp parallel
    {
#pragma omp single
        {
            printf("%lu\n", fibo_par(47)); // ajustez pour durer 8s
        }
    }
    return EXIT_SUCCESS;
}