#include <stdio.h>
#include <string.h>

#include "const.h"
#include "timing.h"
#include "utils.h"

#include "filtre_multi-pas.h"

void generic_jacobi_pas_pair(t_args_wrapper *args_wrapper) {
    if (args_wrapper != NULL) {
        t_jacobi_args *jacobi_args = args_wrapper->jacobi_args;
        if (jacobi_args != NULL) {
            jacobi_pas_pair(jacobi_args->_n, jacobi_args->array, jacobi_args->_m);
        }
    }
}

void generic_jacobi_pas_pair_inplace(t_args_wrapper *args_wrapper) {
    if (args_wrapper != NULL) {
        t_jacobi_args *jacobi_args = args_wrapper->jacobi_args;
        if (jacobi_args != NULL) {
            jacobi_pas_pair_inplace(jacobi_args->_n, jacobi_args->array, jacobi_args->_m);
        }
    }
}

void generic_jacobi_pas_pair_inplace_realloc(t_args_wrapper *args_wrapper) {
    if (args_wrapper != NULL) {
        t_jacobi_args *jacobi_args = args_wrapper->jacobi_args;
        if (jacobi_args != NULL) {
            jacobi_pas_pair_inplace_realloc(jacobi_args->_n, jacobi_args->array, jacobi_args->_m);
        }
    }
}

void generic_jacobi_CA(t_args_wrapper *args_wrapper) {
    if (args_wrapper != NULL) {
        t_jacobi_args *jacobi_args = args_wrapper->jacobi_args;
        if (jacobi_args != NULL) {
            jacobi_CA(jacobi_args->_n, jacobi_args->array, jacobi_args->_m);
        }
    }
}

int main(void) {
    E *array = malloc(n * sizeof *array);
    if (array == NULL) EXIT_FAILURE;
    E *buffer = malloc(n * sizeof *buffer);
    if (buffer == NULL) EXIT_FAILURE;
    random_array1d(array, n);
    memcpy(buffer, array, n * sizeof *buffer);
    
    /* printf("Array A\n");
    display_array(array, n);

    jacobi_pas_pair(n, array, m);
    printf("Array A\n");
    display_array(array, n);
    memcpy(array, buffer, n * sizeof *array);

    jacobi_pas_pair_inplace(n, array, m);
    printf("Array A\n");
    display_array(array, n);
    memcpy(array, buffer, n * sizeof *array);

    jacobi_pas_pair_inplace_realloc(n, array, m);
    memcpy(array, buffer, n * sizeof *array);

    jacobi_CA(n, array, m);
    printf("Array A\n");
    display_array(array, n);
    memcpy(array, buffer, n * sizeof *array); */

    t_jacobi_args jacobi_args = {._n = n, .array = array, ._m = m};
    t_args_wrapper args_wrapper = {.mergesort_args = NULL,
                                   .transposition_args = NULL,
                                   .array2d_min_max_args = NULL,
                                   .jacobi_args = &jacobi_args};
    printf("\njacobi_pas_pair\n");
    generic_fn_execution_time(&args_wrapper, generic_jacobi_pas_pair);
    /* printf("Array A\n");
    display_array(array, n); */
    memcpy(array, buffer, n * sizeof *array);

    // bizarre que ce programme soit si rapide
    printf("\njacobi_pas_pair_inplace_realloc\n");
    generic_fn_execution_time(&args_wrapper, generic_jacobi_pas_pair_inplace_realloc);
    /* printf("Array A\n");
    display_array(array, n); */
    memcpy(array, buffer, n * sizeof *array);

    printf("\njacobi_pas_pair_inplace\n");
    generic_fn_execution_time(&args_wrapper, generic_jacobi_pas_pair_inplace);
    /* printf("Array A\n");
    display_array(array, n); */
    memcpy(array, buffer, n * sizeof *array);

    printf("\njacobi_CA\n");
    generic_fn_execution_time(&args_wrapper, generic_jacobi_CA);
    /* printf("Array A\n");
    display_array(array, n); */

    free(array);
    free(buffer);

    return EXIT_SUCCESS;
}