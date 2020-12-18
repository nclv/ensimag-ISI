#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char** argv) {
    (void)argc;
    (void)argv;
    printf("hello avec %d thread\n", omp_get_num_threads()); // 1 seul thread lancé
    return EXIT_SUCCESS;
}