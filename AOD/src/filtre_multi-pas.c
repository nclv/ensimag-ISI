#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "const.h"
#include "utils.h"

#define sum(a, b, c) ((a) + (b) + (c))

int mod(int a, int b) {
    int r = a % b;
    return r < 0 ? r + b : r;
}

/**
 * @param _m doit être pair
 */ 
void jacobi_pas_pair(size_t _n, E *A, size_t _m) {
    for (size_t t = 0; t < _m; t += 2) {
        E tmp[_n];
        for (size_t i = 0; i < _n; ++i) { // pas 2t + 1
            tmp[i] = sum(A[mod((int)i - 1, (int)_n)], A[i], A[mod((int)i + 1, (int)_n)]);
            // printf("tmp %f\n", tmp[i]);
        }
        for (size_t i = 0; i < _n; ++i) { // pas 2t + 2
            A[i] = sum(tmp[mod((int)i - 1, (int)_n)], tmp[i], tmp[mod((int)i + 1, (int)_n)]);
            // printf("A %f\n", A[i]);
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
    E *tmpA = calloc(_n + 1, sizeof *tmpA);
    if (tmpA == NULL) EXIT_FAILURE;
    for (size_t i = 0; i < _n; ++i) {
        tmpA[i] = A[i];
    }

    for (size_t t = 0; t < _m; ++t) {
        E old = tmpA[_n - 1];  // circulaire
        tmpA[_n] = tmpA[0];  // circulaire
        for (size_t i = 0; i < _n; ++i) { // pas t
            E tmp = tmpA[i];
            tmpA[i] = sum(old, tmpA[i], tmpA[i + 1]);
            old = tmp;
        }
    }
    /* printf("Array tmpA (realloc)\n");
    display_array(tmpA, _n + 1); */
    free(tmpA);
}

/**
 * Calcul du triangle inférieur.
 * 
 * En entrée on a l'horizontale A(i - K, 0) ... A(i + K, 0) stockée dans A[i - K, ..., i + K]. 
 * i est le milieu de l'horizontale
 * 
 * On calcule les diagonales 
 *  - Nord-Ouest: A(i - K + 1, 1), A(i - K + 2, 2), ..., A(i, K) stockée dans A[i - K + 1, ..., i]
 *  - Nord-Est: A(i, K), A(i + 1, K - 1), ..., A(i + K - 1, 1) stockée dans A[i, i + K - 1]
 * et les sous-diagonales
 *  - Nord-Ouest: A(i - K + 1, 0), A(i - K + 2, 0), ..., A(i, K - 1) stockée dans T[i - K + 1, ..., i]
 *  - Nord-Est: A(i, K - 1), A(i + 1, K - 2), ..., A(i + K - 1, 0) stockée dans T[i, i + K - 1]
 */
void Tinf(size_t _n, size_t i, size_t K, E *A, E *T) {
    int nb = (int)(2 * K - 1);  // nombre de points à calculer sur l'horizontale
    int current = (int)(i - K + 1);  // abscisse du premier point
    // printf("%d %ld %ld %ld\n", current, i, K, i - K + 1);
    for (; (nb > 0); current += 1, nb -= 2) {  // on décrémente de 2 car on calcul T et A dans la boucle
        E prev = A[mod((int)current - 1, (int)_n)];  // pour le calcul inplace
        for (int k = 0; k < nb; ++k) {
            int j = mod((int)current + k, (int)_n);
            T[j] = A[j];
            // printf("%f %d %d\n", prev, j, (j + 1) % (int)_n);
            A[j] = sum(prev, T[j], A[mod((int)j + 1, (int)_n)]);
            prev = T[j];
        }
    }
}
/**
 * Calcul du losange carré de côté K contenant les points A[i - K, i + K]
 *
 * En entrée on a les diagonales
 *  - Sud-Ouest: A(i, t), A(i - 1, t + 1), ..., A(i - K, t + K) stockée dans A[i, ..., i - K]
 *  - Sud-Est: A(i, t), A(i + 1, t + 1), ..., A(i + K, t + K) stockée dans A[i, ..., i + K]
 * et les sous-diagonale
 *  - Sud-Ouest: A(i, t - 1), A(i - 1, t), ..., A(i - K, t + K - 1) stockée dans T[i, ..., i - K]
 *  - Sud-Est: A(i, t - 1), A(i + 1, t), ..., A(i + K, t + K - 1) stockée dans T[i, ..., i + K]
 *
 * On calcule les diagonales 
 *  - Nord-Ouest: A(i, t + 2K), A(i - 1, t + 2K - 1), ..., A(i - K + 1, t + K + 1) stockée dans A[i, ..., i - K]
 *  - Nord-Est: A(i, t + 2K), A(i + 1, t + 2K - 1), ..., A(i + K - 1, t + K + 1) stockée dans A[i, ..., i + K]
 * et les sous-diagonales
 *  - Nord-Ouest: A(i, t + 2K - 1), A(i - 1, t + 2K - 2), ..., A(i - K + 1, t + K) stockée dans T[i, ..., i - K]
 *  - Nord-Est: A(i, t + 2K - 1), A(i + 1, t + 2K - 2), ..., A(i + K - 1, t + K) stockée dans T[i, ..., i + K]
 */
void losange(size_t _n, size_t i, size_t K, E *A, E *T) {
    for (size_t t = 0; t < K; ++t) {
        int current = (int)(i + t);
        // printf("current %d %ld %ld\n", current, i, t);
        for (int k = current; k > current - (int)K; --k) {
            // calcul des éléments de la diagonale et de la sous-diagonale Sud-Ouest à partir de current
            int j = mod((int)k, (int)_n);
            // printf("j %d %d %d\n", (j - 1) % (int)_n, j, (j + 1) % (int)_n);
            T[j] = sum(T[mod((int)j - 1, (int)_n)], A[j], T[mod((int)j + 1, (int)_n)]);  // sous-diagonale
            A[j] = sum(A[mod((int)j - 1, (int)_n)], T[j], A[mod((int)j + 1, (int)_n)]);  // diagonale
        }
    }
}

/**
 * Calcul du triangle supérieur.
 * 
 * En entrée on a les diagonales
 *  - Sud-Ouest: A(i, t), A(i - 1, t + 1), ..., A(i - K, t + K) stockée dans A[i, ..., i - K]
 *  - Sud-Est: A(i, t), A(i + 1, t + 1), ..., A(i + K, t + K) stockée dans A[i, ..., i + K]
 * et les sous-diagonale
 *  - Sud-Ouest: A(i, t - 1), A(i - 1, t), ..., A(i - K, t + K - 1) stockée dans T[i, ..., i - K]
 *  - Sud-Est: A(i, t - 1), A(i + 1, t), ..., A(i + K, t + K - 1) stockée dans T[i, ..., i + K]
 * 
 * On calcule l'horizontale A(i - K, t + K) ... A(i + K, t + K) stockée dans A[i - K, ..., i + K].
 */
void Tsup(size_t _n, size_t i, size_t K, E *A, E *T) {
    for (size_t t = 0; t < K; ++t) {  // 2K diagonales à calculer de Sud-Ouest à Nord-Est
        int current = (int)(i + t);
        int k = current;  // les deux diagonales partent de k
        int nb = (int)(K - t);
        // la sous-diagonale à nb points, la diagonale nb - 1 points
        for (nb = (int)(K - t - 1); nb > 0; --k, --nb) {
            // calcul des éléments de la diagonale et de la sous-diagonale Sud-Ouest à partir de current
            int j = mod((int)k, (int)_n);
            T[j] = sum(T[mod((int)j - 1, (int)_n)], A[j], T[mod((int)j + 1, (int)_n)]);  // sous-diagonale
            A[j] = sum(A[mod((int)j - 1, (int)_n)], T[j], A[mod((int)j + 1, (int)_n)]);  // diagonale
        }
        int j = mod((int)k, (int)_n);
        T[j] = A[j];  // sous-diagonale
        A[j] = sum(T[mod((int)j - 1, (int)_n)], A[j], T[mod((int)j + 1, (int)_n)]);  // sous-diagonale
    }
}

void jacobi_CA(size_t _n, E *A, size_t _m) {
    long int Z = sysconf(_SC_LEVEL1_ICACHE_SIZE);
    size_t K = (size_t)Z / 2;  // Z / 2 where Z = 2^15 = 32K
    printf("Z = %ld, K = %ld\n", Z, K);
    K = _m;  // condition m mod K = 1

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