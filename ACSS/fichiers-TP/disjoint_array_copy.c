/*@
    requires n >= 0;
    requires \valid_read(src+(0..n-1));
    requires \valid(dst+(0..n-1));
    requires \separated(src+(0..n-1), dst+(0..n-1));
    ensures dst[0..n-1] == src[0..n-1];
    assigns dst[0..n-1];
*/
void disjoint_array_copy(int *src, int *dst, int n) {
    // ici on recopie de gauche à droite (on pourrait faire de droite à gauche)
    /*@
        loop invariant 0 <= i <= n;
        loop invariant
            \forall int k; 0 <= k < i ==> dst[k] == src[k];
        loop assigns i, dst[0..n-1];
        loop variant n - i;
    */
        for (int i = 0; i < n; i++) {
            dst[i] = src[i];
        }
}
