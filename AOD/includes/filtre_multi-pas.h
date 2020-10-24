#ifndef _FILTRE_MULTI_PAS_
#define _FILTRE_MULTI_PAS_

#include <stdlib.h>

#include "const.h"

extern void jacobi_pas_pair(size_t _n, E *A, size_t _m);
extern void jacobi_pas_pair_inplace(size_t _n, E *A, size_t _m);
extern void jacobi_pas_pair_inplace_realloc(size_t _n, E *A, size_t _m);
extern void jacobi_CA(size_t _n, E *A, size_t _m);

#endif