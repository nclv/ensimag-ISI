#define MAXINT 2147483647

// TODO: do you understand the purpose of this lemma here ? Try to remove it, to see what happens...
/*@ lemma mult_pos_compat: \forall integer x,y; 0 <= x && 0 <= y ==> 0 <= x*y; */

/*@ requires 0 <= x && 0 <= y;
  @ requires x*y <= MAXINT;
  @ assigns \nothing;
  @ ensures \result == x * y;
  @*/
int mult(int x, int y) {
  int z=0;
  
  /*@ loop invariant 0 <= x <= \at(x,Pre) ; 
    @ loop invariant \at(x,Pre)*y==z+x*y ; 
    @ loop assigns z,x ; // nécessaire car sinon on ne sait pas ce que y est devenu
    // on dit que y n'est pas modifié
    @ loop variant x; */
  // alternative au assigns et variant:
  // loop invariant y = \at(y,Pre);
  // loop variant x;

  while (x > 0) {
    // TODO: what is the purpose of this assertion ? Try to remove it, too see what happens...
    /*@ assert 0 <= (x-1)*y; */
    z+=y;
    x--;
  }
  return z;
}


int main() {
  int x=7, y=8, r;

  r=mult(x,y);

  /*@ assert r == x*y; */

  return r;
}
