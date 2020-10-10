#include "utils.h"

#include <stdio.h>
#include <stdlib.h>

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