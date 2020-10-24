#ifndef _TIMING_
#define _TIMING_

#include <stdlib.h>

#include "const.h"

typedef struct mergesort_args {
    size_t _n;
    E *array;
    E *buffer;
} t_mergesort_args;

typedef struct transposition_args {
    double **matrix;
    double **result;
} t_transposition_args;

typedef struct array2d_min_max_args {
    double **matrix;
    double *line;
    double *col;
} t_array2d_min_max_args;

// Wrapper
typedef struct args_wrapper {
    t_mergesort_args *mergesort_args;
    t_transposition_args *transposition_args;
    t_array2d_min_max_args *array2d_min_max_args;
} t_args_wrapper;

extern void generic_fn_execution_time(t_args_wrapper *args_wrapper,
                                      void (*generic_fn)(t_args_wrapper *));

#endif