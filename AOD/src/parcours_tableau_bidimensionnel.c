#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include "const.h"
#include "timing.h"
#include "utils.h"

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

void generic_line_max_col_min(t_mergesort_args *mergesort_args,
                              t_transposition_args *transposition_args,
                              t_array2d_min_max_args *array2d_min_max_args) {
    (void)mergesort_args;
    (void)transposition_args;
    line_max_col_min(array2d_min_max_args->matrix, array2d_min_max_args->line, array2d_min_max_args->col);
}

void generic_line_max_col_min_opti(t_mergesort_args *mergesort_args,
                                   t_transposition_args *transposition_args,
                                   t_array2d_min_max_args *array2d_min_max_args) {
    (void)mergesort_args;
    (void)transposition_args;
    line_max_col_min_opti(array2d_min_max_args->matrix, array2d_min_max_args->line, array2d_min_max_args->col);
}

void generic_line_max_col_min_block(t_mergesort_args *mergesort_args,
                                   t_transposition_args *transposition_args,
                                   t_array2d_min_max_args *array2d_min_max_args) {
    (void)mergesort_args;
    (void)transposition_args;
    line_max_col_min_block(array2d_min_max_args->matrix, array2d_min_max_args->line, array2d_min_max_args->col);
}

int main(void) {
    double **A = allocate_matrix(n, m);
    double *S = malloc(n * sizeof *S);
    double *T = malloc(m * sizeof *T);
    random_matrix2d_dyn(A, n, m);

    // printf("Matrice A\n");
    // display_matrix_dyn(A, n, m);

    // line_max(A, S);
    // printf("Array S\n");
    // display_array(S, n);

    // col_min(A, T);
    // printf("Array T\n");
    // display_array(T, m);

    // line_max_col_min(A, S, T);
    // printf("Array S\n");
    // display_array(S, n);
    // printf("Array T\n");
    // display_array(T, m);

    // line_max_col_min_opti(A, S, T);
    // printf("Array S\n");
    // display_array(S, n);
    // printf("Array T\n");
    // display_array(T, m);

    // line_max_col_min_block(A, S, T);
    // printf("Array S\n");
    // display_array(S, n);
    // printf("Array T\n");
    // display_array(T, m);

    t_array2d_min_max_args array2d_min_max_args = {.matrix = A, .line = S, .col = T};
    printf("\nline_max_col_min\n");
    generic_fn_execution_time(NULL, NULL, &array2d_min_max_args, generic_line_max_col_min);
    printf("\nline_max_col_min_opti\n");
    generic_fn_execution_time(NULL, NULL, &array2d_min_max_args, generic_line_max_col_min_opti);
    printf("\nline_max_col_min_block\n");
    generic_fn_execution_time(NULL, NULL, &array2d_min_max_args, generic_line_max_col_min_block);

    free_matrix(A, n);
    free(S);
    free(T);

    return EXIT_SUCCESS;
}