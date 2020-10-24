#include <stdio.h>
#include <stdlib.h>

#include "const.h"
#include "timing.h"
#include "utils.h"

#include "transposition.h"

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
    if (A == NULL) EXIT_FAILURE;
    double **B = allocate_matrix(n, m);
    if (B == NULL) EXIT_FAILURE;
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
                                   .array2d_min_max_args = NULL,
                                   .jacobi_args = NULL};
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