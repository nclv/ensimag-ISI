#ifndef _UTILS_
#define _UTILS_

#include <stdlib.h>

#include "const.h"

extern double** allocate_matrix(size_t _n, size_t _m);
extern void free_matrix(double** matrix, size_t _n);

extern void random_matrix2d(double matrix[n][m]);
extern void random_matrix2d_dyn(double **matrix, size_t _n, size_t _m);
extern void random_array1d_n(double array[n]);
extern void random_array1d_m(double array[m]);

extern void display_matrix(double matrix[n][m]);
extern void display_matrix_dyn(double **matrix, size_t _n, size_t _m);
extern void display_array(double *array, size_t _n);

#endif