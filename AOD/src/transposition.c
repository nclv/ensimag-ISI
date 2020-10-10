#include <assert.h>
#include <math.h>
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include "utils.h"

static double A[n][m];
static double B[n][m];

void transpose_ligne(double matrix[n][m], double result[n][m]) {
    for (size_t i = 0; i < m; ++i) {
        for (size_t j = 0; j < n; ++j) {
            result[j][i] = matrix[i][j];
        }
    }
}

void transpose_block(double matrix[n][m], double result[n][m]) {
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

void transpose_rec_aux(double matrix[n][m], double result[n][m],
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

void transpose_rec(double matrix[n][m], double result[n][m]) {
    long int Z = sysconf(_SC_LEVEL1_ICACHE_SIZE);
    size_t S = (size_t)sqrt((double)Z / 2);  // sqrt(Z / 2) where Z = 2^15 = 32K
    printf("Z = %ld, K = %ld\n", Z, S);

    transpose_rec_aux(matrix, result, 0, m, 0, n, 0, n, 0, m, S);
}

void functions_execution_time(double matrix[n][m], double result[n][m],
                              void (*transposition_function)(double[n][m], double[n][m])) {
    static clock_t start, end;
    static double cpu_time_used;

    start = clock();
    (*transposition_function)(matrix, result);
    end = clock();
    cpu_time_used = ((double)(end - start)) / CLOCKS_PER_SEC;

    printf("CPU time used: %lf\n", cpu_time_used);
    // printf("%s took %f seconds to execute for an entry n = %ld\n", function_name, cpu_time_used, n);
}

int main(void) {
    random_matrix2d(A);

    // printf("Matrice A\n");
    // display_matrix(A);

    // transpose_ligne(A, B);
    // printf("Matrice B\n");
    // display_matrix(B);

    // transpose_block(A, B);
    // printf("Matrice B\n");
    // display_matrix(B);

    // transpose_rec(A, B);
    // printf("Matrice B\n");
    // display_matrix(B);

    printf("\ntranspose_ligne\n");
    functions_execution_time(A, B, transpose_ligne);
    printf("\ntranspose_block\n");
    functions_execution_time(A, B, transpose_block);
    printf("\ntranspose_rec\n");
    functions_execution_time(A, B, transpose_rec);

    return EXIT_SUCCESS;
}