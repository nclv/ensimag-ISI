#include <omp.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char** argv) {
    (void)argc;
    (void)argv;

#pragma omp parallel
    {
        // pour changer l'ordonnancement de la boucle, ajoutez à la directive for l'option schedule(dynamic), schedule(static) ou bien schedule(guided)
#pragma omp for
        for (int i = 0; i < 25; i++) {
            printf("hello[%d] de %d/%d\n", i, omp_get_thread_num(), omp_get_num_threads());
        }
    }
    return EXIT_SUCCESS;
}