#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint64_t fibo_seq(uint32_t n) {
    if (n < 2)
        return n;

    return fibo_seq(n - 1) + fibo_seq(n - 2);
}

int main(int argc, char** argv) {
    (void)argc;
    (void)argv;

    printf("%lu\n", fibo_seq(47)); // ajustez pour durer 8s
    return EXIT_SUCCESS;
}