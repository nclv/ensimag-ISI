#include "timing.h"

#include <stdio.h>
#include <time.h>

void generic_fn_execution_time(t_mergesort_args *mergesort_args,
                               t_transposition_args *transposition_args,
                               t_array2d_min_max_args *array2d_min_max_args,
                               void (*generic_fn)(t_mergesort_args *, t_transposition_args *, t_array2d_min_max_args *)) {
    static clock_t start, end;
    static double cpu_time_used;

    start = clock();
    (*generic_fn)(mergesort_args, transposition_args, array2d_min_max_args);
    end = clock();
    cpu_time_used = ((double)(end - start)) / CLOCKS_PER_SEC;

    printf("CPU time used: %lf\n", cpu_time_used);
}