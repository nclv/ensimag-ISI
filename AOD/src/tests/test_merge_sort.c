#include <stdio.h>

#include "const.h"
#include "timing.h"
#include "utils.h"

#include "merge_sort.h"

void generic_mergesort(t_args_wrapper *args_wrapper) {
    if (args_wrapper != NULL) {
        t_mergesort_args *mergesort_args = args_wrapper->mergesort_args;
        if (mergesort_args != NULL) {
            mergesort(mergesort_args->_n, mergesort_args->array, mergesort_args->buffer);
        }
    }
}

int main(void) {
    E *array = malloc(n * sizeof *array);
    E *buffer = calloc(n, sizeof *buffer);
    random_array1d(array, n);

    // display_array(array, n);
    // display_array(buffer, n);

    // mergesort(n, array, buffer);

    // display_array(array, n);

    printf("\nmergesort\n");
    t_mergesort_args mergesort_args = {._n = n, .array = array, .buffer = buffer};
    t_args_wrapper args_wrapper = {.mergesort_args = &mergesort_args,
                                   .transposition_args = NULL,
                                   .array2d_min_max_args = NULL};
    generic_fn_execution_time(&args_wrapper, generic_mergesort);

    free(buffer);
    free(array);

    return EXIT_SUCCESS;
}