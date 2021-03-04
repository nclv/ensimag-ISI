// TODO : mettre les bonnes annotations...

/*@
    requires n >= 0;
    requires \valid_read(src+(0..n-1));
    requires \valid(dst+(0..n-1));
    assigns dst[0..n-1];
    ensures dst[0..n-1] == \old(src[0..n-1]);
*/
void array_copy(int *src, int *dst, int n) {
    if (src < dst) {
        // recopier de droite à gauche
        /*@ loop assigns i, dst[0..n-1]; */
        for (int i = n-1; -1 < i; i--) {
            dst[i] = src[i];
        }
    } else {
        // recopier de gauche à droite
        /*@ loop assigns i, dst[0..n-1]; */
        for (int i = 0; i < n; i++) {
            dst[i] = src[i];
        }
    }
}
