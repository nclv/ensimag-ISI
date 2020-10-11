#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include "timing.h"
#include "utils.h"

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

void generic_mergesort(t_mergesort_args *mergesort_args,
                       t_transposition_args *transposition_args,
                       t_array2d_min_max_args *array2d_min_max_args) {
    (void)transposition_args;
    (void)array2d_min_max_args;
    mergesort(mergesort_args->_n, mergesort_args->array, mergesort_args->buffer);
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
    t_mergesort_args mergesort_args = {._n = n, .array = array, .buffer = buffer};
    generic_fn_execution_time(&mergesort_args, NULL, NULL, generic_mergesort);

    free(buffer);
    free(array);

    return EXIT_SUCCESS;
}