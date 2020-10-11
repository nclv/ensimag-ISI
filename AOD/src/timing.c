#include "timing.h"

#include <stdio.h>
#include <time.h>

void generic_fn_execution_time(t_args_wrapper *args_wrapper,
                               void (*generic_fn)(t_args_wrapper *)) {
    static clock_t start, end;
    static double cpu_time_used;

    start = clock();
    (*generic_fn)(args_wrapper);
    end = clock();
    cpu_time_used = ((double)(end - start)) / CLOCKS_PER_SEC;

    printf("CPU time used: %lf\n", cpu_time_used);
}