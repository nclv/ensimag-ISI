#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include "utils.h"

typedef double E;

void merge(size_t _n, E *A, size_t _m, E *B, E *X) {
    size_t k, ptA, ptB;
    for (k = 0, ptA = 0, ptB = 0; (ptA != _n) && (ptB != _m); ++k) {
        if (B[ptB] < A[ptA]) {
            X[k] = B[ptB];
            ptB += 1;
        } else {
            X[k] = A[ptA];
            ptA += 1;
        }
    }
    while (ptA != _n) {
        X[k] = A[ptA];
        ptA += 1;
        k += 1;
    }
    while (ptB != _m) {
        X[k] = B[ptB];
        ptB += 1;
        k += 1;
    }
}

void mergesort(size_t _n, E *T, E *U) {
    if (_n > 1) {
        mergesort(_n / 2, T, U);
        mergesort(_n - _n / 2, T + _n / 2, U + _n / 2);
        merge(_n / 2, T, _n - _n / 2, T + _n / 2, U);
        for (size_t i = 0; i < _n; ++i) {
            T[i] = U[i];
        }
    }
}

void functions_execution_time(size_t _n, E *array, E *buffer,
                              void (*mergesort_function)(size_t, E *, E *)) {
    static clock_t start, end;
    static double cpu_time_used;

    start = clock();
    (*mergesort_function)(_n, array, buffer);
    end = clock();
    cpu_time_used = ((double)(end - start)) / CLOCKS_PER_SEC;

    printf("CPU time used: %lf\n", cpu_time_used);
    // printf("%s took %f seconds to execute for an entry n = %ld\n", function_name, cpu_time_used, n);
}

int main(void) {
    E *array = malloc(n * sizeof *array);
    E *buffer = calloc(n, sizeof *buffer);
    random_array1d_n(array);

    // display_array_n(array);
    // display_array_n(buffer);

    // // array2 is our buffer
    // mergesort(n, array, buffer);

    // display_array_n(array);

    printf("\nmergesort\n");
    functions_execution_time(n, array, buffer, mergesort);

    free(buffer);
    free(array);

    return EXIT_SUCCESS;
}