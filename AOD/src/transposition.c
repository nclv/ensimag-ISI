#include <assert.h>
#include <math.h>
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include "const.h"
#include "timing.h"
#include "utils.h"

void transpose_ligne(double **matrix, double **result) {
    for (size_t i = 0; i < m; ++i) {
        for (size_t j = 0; j < n; ++j) {
            result[j][i] = matrix[i][j];
        }
    }
}

void transpose_block(double **matrix, double **result) {
    long int Z = sysconf(_SC_LEVEL1_ICACHE_SIZE);
    size_t K = (size_t)sqrt((double)Z / 2);  // sqrt(Z / 2) where Z = 2^15 = 32K
    printf("Z = %ld, K = %ld\n", Z, K);

    size_t maxi;
    size_t maxj;
    for (size_t I = 0; I < m; I += K) {
        for (size_t J = 0; J < n; J += K) {
            maxi = (m < I + K) ? m : I + K;
            maxj = (n < J + K) ? n : J + K;
            for (size_t i = I; i < maxi; ++i) {
                for (size_t j = J; j < maxj; ++j) {
                    result[j][i] = matrix[i][j];
                }
            }
        }
    }
}

void transpose_rec_aux(double **matrix, double **result,
                       size_t mAb, size_t mAe, size_t nAb, size_t nAe,
                       size_t mBb, size_t mBe, size_t nBb, size_t nBe,
                       size_t S) {
    assert(((mAe - mAb) == (nBe - nBb)) && ((nAe - nAb) == (mBe - mBb)));

    // static size_t count = 0;
    // count++;
    // printf("%li, ", count);

    size_t _m = mAe - mAb;
    size_t _n = nAe - nAb;
    if ((_n <= S) && (_m <= S)) {
        size_t iA, jA, iB, jB;
        for (iA = mAb, jB = nBb; iA < mAe; ++iA, ++jB) {
            for (jA = nAb, iB = mBb; jA < nAe; ++jA, ++iB) {
                result[iB][jB] = matrix[iA][jA];
            }
        }
    } else {
        if (_m > _n) {
            size_t mid = _m / 2;
#pragma omp task
            { transpose_rec_aux(matrix, result, mAb + mid, mAe, nAb, nAe, mBb, mBe, nBb + mid, nBe, S); }
            transpose_rec_aux(matrix, result, mAb, mAb + mid, nAb, nAe, mBb, mBe, nBb, nBb + mid, S);
        } else {
            size_t mid = _n / 2;
#pragma omp task
            { transpose_rec_aux(matrix, result, mAb, mAe, nAb + mid, nAe, mBb + mid, mBe, nBb, nBe, S); }
            transpose_rec_aux(matrix, result, mAb, mAb, nAb, nAb + mid, mBb, mBb + mid, nBb, nBb, S);
        }
    }
}

void transpose_rec(double **matrix, double **result) {
    long int Z = sysconf(_SC_LEVEL1_ICACHE_SIZE);
    size_t S = (size_t)sqrt((double)Z / 2);  // sqrt(Z / 2) where Z = 2^15 = 32K
    printf("Z = %ld, K = %ld\n", Z, S);

    transpose_rec_aux(matrix, result, 0, m, 0, n, 0, n, 0, m, S);
}

void generic_transpose_ligne(t_args_wrapper *args_wrapper) {
    if (args_wrapper != NULL) {
        t_transposition_args *transposition_args = args_wrapper->transposition_args;
        if (transposition_args != NULL) {
            transpose_ligne(transposition_args->matrix, transposition_args->result);
        }
    }
}

void generic_transpose_block(t_args_wrapper *args_wrapper) {
    if (args_wrapper != NULL) {
        t_transposition_args *transposition_args = args_wrapper->transposition_args;
        if (transposition_args != NULL) {
            transpose_block(transposition_args->matrix, transposition_args->result);
        }
    }
}

void generic_transpose_rec(t_args_wrapper *args_wrapper) {
    if (args_wrapper != NULL) {
        t_transposition_args *transposition_args = args_wrapper->transposition_args;
        if (transposition_args != NULL) {
            transpose_rec(transposition_args->matrix, transposition_args->result);
        }
    }
}

int main(void) {
    double **A = allocate_matrix(n, m);
    double **B = allocate_matrix(n, m);
    random_matrix2d_dyn(A, n, m);

    // printf("Matrice A\n");
    // display_matrix_dyn(A, n, m);

    // transpose_ligne(A, B);
    // printf("Matrice B\n");
    // display_matrix_dyn(B, n, m);

    // transpose_block(A, B);
    // printf("Matrice B\n");
    // display_matrix_dyn(B, n, m);

    // transpose_rec(A, B);
    // printf("Matrice B\n");
    // display_matrix_dyn(B, n, m);

    t_transposition_args transposition_args = {.matrix = A, .result = B};
    t_args_wrapper args_wrapper = {.mergesort_args = NULL,
                                   .transposition_args = &transposition_args,
                                   .array2d_min_max_args = NULL};
    printf("\ntranspose_ligne\n");
    generic_fn_execution_time(&args_wrapper, generic_transpose_ligne);
    printf("\ntranspose_block\n");
    generic_fn_execution_time(&args_wrapper, generic_transpose_block);
    printf("\ntranspose_rec\n");
    generic_fn_execution_time(&args_wrapper, generic_transpose_rec);

    free_matrix(A, n);
    free_matrix(B, n);

    return EXIT_SUCCESS;
}