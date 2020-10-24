#include <stdio.h>

#include "const.h"
#include "timing.h"
#include "utils.h"

#include "parcours_tableau_bidimensionnel.h"

void generic_line_max_col_min(t_args_wrapper *args_wrapper) {
    if (args_wrapper != NULL) {
        t_array2d_min_max_args *array2d_min_max_args = args_wrapper->array2d_min_max_args;
        if (array2d_min_max_args != NULL) {
            line_max_col_min(array2d_min_max_args->matrix, array2d_min_max_args->line, array2d_min_max_args->col);
        }
    }
}

void generic_line_max_col_min_opti(t_args_wrapper *args_wrapper) {
    if (args_wrapper != NULL) {
        t_array2d_min_max_args *array2d_min_max_args = args_wrapper->array2d_min_max_args;
        if (array2d_min_max_args != NULL) {
            line_max_col_min_opti(array2d_min_max_args->matrix, array2d_min_max_args->line, array2d_min_max_args->col);
        }
    }
}

void generic_line_max_col_min_block(t_args_wrapper *args_wrapper) {
    if (args_wrapper != NULL) {
        t_array2d_min_max_args *array2d_min_max_args = args_wrapper->array2d_min_max_args;
        if (array2d_min_max_args != NULL) {
            line_max_col_min_block(array2d_min_max_args->matrix, array2d_min_max_args->line, array2d_min_max_args->col);
        }
    }
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
    t_args_wrapper args_wrapper = {.mergesort_args = NULL,
                                   .transposition_args = NULL,
                                   .array2d_min_max_args = &array2d_min_max_args};
    printf("\nline_max_col_min\n");
    generic_fn_execution_time(&args_wrapper, generic_line_max_col_min);
    printf("\nline_max_col_min_opti\n");
    generic_fn_execution_time(&args_wrapper, generic_line_max_col_min_opti);
    printf("\nline_max_col_min_block\n");
    generic_fn_execution_time(&args_wrapper, generic_line_max_col_min_block);

    free_matrix(A, n);
    free(S);
    free(T);

    return EXIT_SUCCESS;
}