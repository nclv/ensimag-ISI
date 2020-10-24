#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "const.h"

#define sum(a, b, c) ((a) + (b) + (c))

void jacobi_pas_pair(size_t _n, E *A, size_t _m) {
    for (size_t t = 0; t < _m; t += 2) {
        E tmp[_n];
        for (size_t i = 0; i < _n; ++i) { // pas 2t + 1
            tmp[i] = sum(A[(i - 1) % _n], A[i], A[(i + 1) % _n]);
        }
        for (size_t i = 0; i < _n; ++i) { // pas 2t + 2
            A[i] = sum(tmp[(i - 1) % _n], tmp[i], tmp[(i + 1) % _n]);
        }
    }
}

void jacobi_pas_pair_inplace(size_t _n, E *A, size_t _m) {
    for (size_t t = 0; t < _m; ++t) {
        E first = A[0];
        E old = A[0];
        A[0] = sum(A[_n - 1], A[0], A[1]);
        for (size_t i = 1; i < _n - 1; ++i) { // pas t
            E tmp = A[i];
            A[i] = sum(old, A[i], A[i + 1]);
            old = tmp;
        }
        A[_n - 1] = sum(old, A[_n - 1], first);
    }
}

// on peut améliorer cette solution en faisant la boucle de _n − 1 à 0 et en utilisant A[-1].
void jacobi_pas_pair_inplace_realloc(size_t _n, E *A, size_t _m) {
    // reallocation pour avoir A[_n] = A[0]
    E *tmpA = realloc(A, (_n + 1) * sizeof *tmpA);
    if (tmpA == NULL) EXIT_FAILURE;
    A = tmpA;

    for (size_t t = 0; t < _m; ++t) {
        E old = A[_n - 1];  // circulaire
        A[_n] = A[0];  // circulaire
        for (size_t i = 0; i < _n; ++i) { // pas t
            E tmp = A[i];
            A[i] = sum(old, A[i], A[i + 1]);
            old = tmp;
        }
    }

    // reallocation pour revenir à A de taille _n
    tmpA = realloc(A, _n * sizeof *tmpA);
    if (tmpA == NULL) EXIT_FAILURE;
    A = tmpA;
}

/**
 * Calcul du triangle inférieur.
 * 
 * En entrée on a l'horizontale A(i - K, 0) ... A(i + K, 0) stockée dans
 * A[i - K, ..., i + K]. i est le milieu de l'horizontale
 * 
 * On calcule les diagonales 
 *  - Nord-Ouest: A(i - K + 1, 1), A(i - K + 2, 2), ..., A(i, K) stockée dans A[i - K + 1, ..., i]
 *  - Nord-Est: A(i, K), A(i + 1, K - 1), ..., A(i + K - 1, 1) stockée dans A[i, i + K - 1]
 * et les sous-diagonales
 *  - Nord-Ouest: A(i - K + 1, 0), A(i - K + 2, 0), ..., A(i, K - 1) stockée dans T[i - K + 1, ..., i]
 *  - Nord-Est: A(i, K - 1), A(i + 1, K - 2), ..., A(i + K - 1, 0) stockée dans T[i, i + K - 1]
 */
void Tinf(size_t _n, size_t i, size_t K, E *A, E *T) {
    int nb = 2 * K - 1;  // nombre de points à calculer sur l'horizontale
    int current = i - K + 1;  // abscisse du premier point
    for (; (nb > 0); current += 1, nb -= 2) {  // on décrémente de 2 car on calcul T et A dans la boucle
        E prev = A[(current - 1) % _n];  // pour le calcul inplace
        for (int k = 0; k < nb; ++k) {
            int j = (current + k) % _n;
            T[j] = A[j];
            A[j] = sum(prev, T[j], A[(j + 1) % _n]);
            prev = T[j];
        }
    }
}

void losange(size_t _n, size_t i, size_t K, E *A, E *T) {}

/**
 * Calcul du triangle supérieur.
 * 
 * En entrée on a les diagonales
 *  - Sud-Ouest:
 *  - Sud-Est:
 * et les sous-diagonale
 *  - Sud-Ouest:
 *  - Sud-Est:
 * 
 * On calcule l'horizontale A(i - K, t + K) ... A(i + K, t + K) stockée dans
 * A[i - K, ..., i + K].
 */
void Tsup(size_t _n, size_t i, size_t K, E *A, E *T) {

}

void jacobi_CA(size_t _n, E *A, size_t _m) {
    long int Z = sysconf(_SC_LEVEL1_ICACHE_SIZE);
    size_t K = (size_t)Z / 2;  // Z / 2 where Z = 2^15 = 32K
    printf("Z = %ld, K = %ld\n", Z, K);

    // Initialisation de T pour éviter les modulos
    E *T = malloc(_n * sizeof *T);
    memcpy(T, A, _n * sizeof *T);
    // triangle inférieur
    for (size_t i = 0; i < _n; i += 2 * K) {
        Tinf(_n, i, K, A, T);
    }
    for (size_t t = 0; t < _m / K - 1; ++t) {
        // calcul des losanges à partir de A((t + K) % _n, t + 1) (point Sud-Ouest)
        for (size_t i = (((t % 2) == 0) ? K : 0); i < _n; i += 2 * K) {
            losange(_n, i, K, A, T);
        }
    }
    // triangle supérieur
    for (size_t i = ((((_m / K) % 2) == 0) ? 0 : K); i < _n; i += 2 * K) {
        Tsup(_n, i, K, A, T);
    }
    free(T);
}