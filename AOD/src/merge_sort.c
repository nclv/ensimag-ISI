#include <stdlib.h>
#include <unistd.h>

#include "const.h"

void merge(size_t _n, E *A, size_t _m, E *B, E *X) {
    size_t k, ptA, ptB;
    for (k = 0, ptA = 0, ptB = 0; (ptA != _n) && (ptB != _m); ++k) {
        if (B[ptB] < A[ptA]) {
            X[k] = B[ptB];
            ptB += 1;
        } else {
            X[k] = A[ptA];
            ptA += 1;
        }
    }
    while (ptA != _n) {
        X[k] = A[ptA];
        ptA += 1;
        k += 1;
    }
    while (ptB != _m) {
        X[k] = B[ptB];
        ptB += 1;
        k += 1;
    }
}

void mergesort(size_t _n, E *T, E *U) {
    if (_n > 1) {
        mergesort(_n / 2, T, U);
        mergesort(_n - _n / 2, T + _n / 2, U + _n / 2);
        merge(_n / 2, T, _n - _n / 2, T + _n / 2, U);
        for (size_t i = 0; i < _n; ++i) {
            T[i] = U[i];
        }
    }
}