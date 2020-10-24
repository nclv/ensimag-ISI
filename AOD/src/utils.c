#include "utils.h"

#include <stdio.h>
#include <stdlib.h>

#include "const.h"

double** allocate_matrix(size_t _n, size_t _m) {
    double** matrix = malloc(_n * sizeof(double*));
    if (matrix == NULL) EXIT_FAILURE;
    size_t i;

    for (i = 0; i < _n; ++i) {
        matrix[i] = malloc(_m * sizeof(double));
        if (matrix[i] == NULL) EXIT_FAILURE;
    }
    return matrix;
}

void free_matrix(double** matrix, size_t _n) {
    for (size_t i = 0; i < _n; ++i) {
        free(matrix[i]);
    }
    free(matrix);
}

void random_matrix2d_dyn(double **matrix, size_t _n, size_t _m) {
    for (size_t i = 0; i < _n; ++i) {
        for (size_t j = 0; j < _m; ++j) {
            matrix[i][j] = RANGE * ((double)rand() / RAND_MAX);
        }
    }
}

void random_array1d(double *array, size_t _n) {
    for (size_t i = 0; i < _n; ++i) {
        array[i] = RANGE * ((double)rand() / RAND_MAX);
    }
}

void display_matrix_dyn(double **matrix, size_t _n, size_t _m) {
    for (size_t i = 0; i < _n; ++i) {
        for (size_t j = 0; j < _m; ++j) {
            printf("%04.1f ", matrix[i][j]);
        }
        printf("\n");
    }
}

void display_array(double *array, size_t _n) {
    for (size_t i = 0; i < _n; ++i) {
        printf("%04.1f ", array[i]);
    }
    printf("\n");
}
