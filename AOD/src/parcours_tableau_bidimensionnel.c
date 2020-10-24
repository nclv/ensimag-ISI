#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "const.h"

// static double A[n][m];
// static double S[n];
// static double T[m];

void line_max(double **matrix, double *array) {
    for (size_t i = 0; i < n; ++i) {
        array[i] = matrix[i][0];
        for (size_t j = 1; j < m; ++j) {
            if (array[i] < matrix[i][j]) {
                array[i] = matrix[i][j];
            }
        }
    }
}

void col_min(double **matrix, double *array) {
    for (size_t j = 0; j < m; ++j) {
        array[j] = matrix[0][j];
    }
    for (size_t i = 1; i < n; ++i) {
        for (size_t j = 0; j < m; ++j) {
            if (array[j] > matrix[i][j]) {
                array[j] = matrix[i][j];
            }
        }
    }
}

void line_max_col_min(double **matrix, double *array_line, double *array_col) {
    // Initialisation
    for (size_t i = 0; i < n; ++i) {
        array_line[i] = __FLT_MIN__;
    }
    for (size_t j = 0; j < m; ++j) {
        array_col[j] = __FLT_MAX__;
    }

    // Calcul
    for (size_t i = 0; i < n; ++i) {
        for (size_t j = 0; j < m; ++j) {
            if (array_col[j] > matrix[i][j]) {
                array_col[j] = matrix[i][j];
            }
            if (array_line[i] < matrix[i][j]) {
                array_line[i] = matrix[i][j];
            }
        }
    }
}

void line_max_col_min_opti(double **matrix, double *array_line, double *array_col) {
    // Initialisation i = 0
    for (size_t j = 0; j < m; ++j) {
        array_col[j] = matrix[0][j];
        if (array_line[0] < matrix[0][j]) {
            array_line[0] = matrix[0][j];
        }
    }

    // Calcul
    for (size_t i = 1; i < n; ++i) {
        array_line[i] = matrix[i][0];
        if (array_col[0] > matrix[i][0]) {
            array_col[0] = matrix[i][0];
        }
        for (size_t j = 1; j < m; ++j) {
            if (array_col[j] > matrix[i][j]) {
                array_col[j] = matrix[i][j];
            }
            if (array_line[i] < matrix[i][j]) {
                array_line[i] = matrix[i][j];
            }
        }
    }
}

void line_max_col_min_block(double **matrix, double *array_line, double *array_col) {
    long int Z = sysconf(_SC_LEVEL1_ICACHE_SIZE);
    size_t K = (size_t)sqrt((double)Z);  // sqrt(Z) where Z = 2^15 = 32K
    printf("Z = %ld, K = %ld\n", Z, K);

    // Initialisation
    for (size_t i = 0; i < n; ++i) {
        array_line[i] = __FLT_MIN__;
    }
    for (size_t j = 0; j < m; ++j) {
        array_col[j] = __FLT_MAX__;
    }

    size_t maxi;
    size_t maxj;
    // Calcul
    for (size_t I = 1; I < n; I += K) {
        for (size_t J = 1; J < m; J += K) {
            maxi = (n < I + K) ? n : I + K;
            maxj = (m < J + K) ? m : J + K;
            for (size_t i = 0; i < maxi; ++i) {
                for (size_t j = 0; j < maxj; ++j) {
                    if (array_col[j] > matrix[i][j]) {
                        array_col[j] = matrix[i][j];
                    }
                    if (array_line[i] < matrix[i][j]) {
                        array_line[i] = matrix[i][j];
                    }
                }
            }
        }
    }
}