#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char** argv) {
    (void)argc;
    (void)argv;

#pragma omp parallel
    { printf("hello de %d/%d\n", omp_get_thread_num(), omp_get_num_threads() - 1); }
    return EXIT_SUCCESS;
}