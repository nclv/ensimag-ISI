#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char** argv) {
    (void)argc;
    (void)argv;

#pragma omp parallel
    {
#pragma omp single // n'importe quel thread
        {
            printf("hello de %d/%d\n", omp_get_thread_num(), omp_get_num_threads());
        }
    }
    return EXIT_SUCCESS;
}