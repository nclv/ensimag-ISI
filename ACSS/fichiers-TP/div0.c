#include "any.h"

// TODO: makes the precondition stronger (but should remain prouvable in main function) !
/*@ requires 0 <= x ;
  @ requires y >= 1;
  @ assigns \nothing;
  @ ensures \result * y <= x;
  @ ensures x - \result * y < y;
  @ ensures \exists int r ;
  @  x == y * \result + r && 0 <= r && r < y;
  @*/
int div(int x,int y) {
  int i=0;
  
  // TODO: fix loop annotations
  /*@ loop invariant x >= 0 && i >=0 && \at(x, Pre) == x + y * i; // \at(x, Pre) - y * i < y && y * i <= \at(x, Pre) 
    @ loop assigns i, x; // FIX ME
    @ loop variant (x + 1) - y; */ // FIX ME
  while (y <= x) {
    i++;
    x-=y;
  }
  /*@
    assert 0 <= x < y; */
  return i;
}


int main() {
  int x=any(), y=any(), q;

  if (x < 0) x=0;
  if (y < 1) y=1;

  q=div(x,y);

  /*@ assert q*y <= x; */
  /*@ assert x-q*y < y; */

  return q;
}
