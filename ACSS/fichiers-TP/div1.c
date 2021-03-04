#include "any.h"

// TODO: 
//   makes the precondition stronger (but should remain prouvable in main function) !
//   fix clause assigns and ensures.
//   1. use option "-wp-model ref" on command line (this assumes absence of aliases on reference parameters).
//   2. remove unsound "-wp-model ref" option (see "buggy" function below).
/*@ requires 0 <= x ; // FIX ME
  @ assigns \nothing; // FIX ME
  @ ensures *r==y;    // FIX ME
  @*/
void div(int x,int y, int* q, int* r) {
  int i=0;

  // TODO: fix loop annotations (cf. div0.c)
  /*@ loop invariant 0;   // FIX ME 
    @ loop assigns \nothing ; // FIX ME
    @ loop variant 0; */  // FIX ME
  while (y <= x) {
    i++;
    x-=y;
  }
  *q=i;
  *r=x;
}

/* The call to div in this buggy function should be rejected,
   otherwise we are able to prove 0==1

   Actually, this is a simple test to detect if the memory model of
   Frama-C is unsound !
     
   TODO: when everything is else green, check that the precondition of this call is rejected.
   In this case, you can comment the function !
   (otherwise: remove "-wp-model ref" option).
  
*/
void buggy() {
  int a = 10;
  div(2*a, a-7, &a, &a);      
  /*@ assert 0 == 1 ; */
}




int main() {
  int x=any(), y=any(), q, r;

  if (x < 0) x=0;
  if (y < 1) y=1;

  div(x,y,&q,&r);

  /*@ assert 0 <= r ; */
  /*@ assert r < y; */
  /*@ assert x==q*y+r; */

  return q;
}
