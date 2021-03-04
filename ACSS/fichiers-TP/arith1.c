#include "any.h"

int main() {
     
  int x = any();
  int y = 0;
  int z = 1;
  
  if (x <= -5 || x >= 20) { x=20; }
  /*@ assert -5 <= x <= 20; */

L: /* exemple d'un label du C */
  
  // TODO 1: modify this loop annotations in order to ensure assertions below.
  // TODO 2: can you add a variant in order to ensure termination of the loop ?
  /*@ 
    loop invariant \at(x,L) <= x <= 20; // x increases !
    // loop invariant y <= 2*x;
    // loop invariant \at(x,L) * 2 == y + 2*x;
    loop assigns x,y;
    loop variant x;
    */  
  while (x <= 19) {
    x++;
    y+=2;
  }

  /*@ assert (y<=48); */
  /*@ assert (z==1); */
  
  return y;
}
