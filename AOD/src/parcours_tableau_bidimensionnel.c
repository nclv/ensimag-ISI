#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#define n (1000)
#define m (1000)
#define RANGE (100)

static double A[n][m];
static double S[n];
static double T[m];

void random_matrix2d(double matrix[n][m]) {
    for (size_t i = 0; i < n; ++i) {
        for (size_t j = 0; j < m; ++j) {
            matrix[i][j] = RANGE * ((double)rand() / RAND_MAX);
        }
    }
}

void display_matrix(double matrix[n][m]) {
    for (size_t i = 0; i < n; ++i) {
        for (size_t j = 0; j < m; ++j) {
            printf("%04.1f ", matrix[i][j]);
        }
        printf("\n");
    }
}

void display_array(double array[n]) {
    for (size_t i = 0; i < n; ++i) {
        printf("%04.1f ", array[i]);
    }
    printf("\n");
}

void line_max(double matrix[n][m], double array[n]) {
    for (size_t i = 0; i < n; ++i) {
        array[i] = matrix[i][0];
        for (size_t j = 1; j < m; ++j) {
            if (array[i] < matrix[i][j]) {
                array[i] = matrix[i][j];
            }
        }
    }
}

void col_min(double matrix[n][m], double array[m]) {
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

void line_max_col_min(double matrix[n][m], double array_line[n], double array_col[m]) {
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

void line_max_col_min_opti(double matrix[n][m], double array_line[n], double array_col[m]) {
    // Initialisation i = 0
    for (size_t j = 0; j < m; ++j) {
        array_col[j] = A[0][j];
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

void line_max_col_min_block(double matrix[n][m], double array_line[n], double array_col[m]) {
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

void functions_execution_time(double matrix[n][m], double array_line[n], double array_col[m],
                              void (*line_max_col_min_function)(double[n][m], double[n], double[m])) {
    static clock_t start, end;
    static double cpu_time_used;

    start = clock();
    (*line_max_col_min_function)(matrix, array_line, array_col);
    end = clock();
    cpu_time_used = ((double)(end - start)) / CLOCKS_PER_SEC;

    printf("CPU time used: %lf\n", cpu_time_used);
    // printf("%s took %f seconds to execute for an entry n = %ld\n", function_name, cpu_time_used, n);
}

int main(void) {
    random_matrix2d(A);

    // printf("Matrice A\n");
    // display_matrix(A);

    // line_max(A, S);
    // printf("Array S\n");
    // display_array(S);

    // col_min(A, T);
    // printf("Array T\n");
    // display_array(T);

    // line_max_col_min(A, S, T);
    // printf("Array S\n");
    // display_array(S);
    // printf("Array T\n");
    // display_array(T);

    // line_max_col_min_opti(A, S, T);
    // printf("Array S\n");
    // display_array(S);
    // printf("Array T\n");
    // display_array(T);

    // line_max_col_min_block(A, S, T);
    // printf("Array S\n");
    // display_array(S);
    // printf("Array T\n");
    // display_array(T);

    printf("\nline_max_col_min\n");
    functions_execution_time(A, S, T, line_max_col_min);
    printf("\nline_max_col_min_opti\n");
    functions_execution_time(A, S, T, line_max_col_min_opti);
    printf("\nline_max_col_min_block\n");
    functions_execution_time(A, S, T, line_max_col_min_block);

    return EXIT_SUCCESS;
}