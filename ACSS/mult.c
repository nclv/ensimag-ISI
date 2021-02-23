/*@ 
  requires 0 <= x ;
  requires 0 <= y;
  requires x*y <= 2147483647;
  assigns \nothing ;
  ensures \result == x * y;
*/
int mult(int x, int y) {
    int z = 0;
    /*@ 
      loop invariant 0 <= x;
      loop invariant \at(x,Pre)*y==z+x*y ;
      loop assigns z,x ;
    */
    while (x > 0) {
        z += y;
        x--;
    }
    return z;
}