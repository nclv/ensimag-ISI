/* SORTING AN ARRAY BY SELECTION OF ITS SUCCESSIVE MINIMUMS.
 */

/*@ requires i < n;
  @ requires \valid(t+(i..n-1));
  @ assigns \nothing;
  @ ensures i <= \result < n ;
  @ ensures \forall int k; i <= k < n ==> t[\result] <= t[k];
  @*/
int minimum(int t[], int i,int n) {
  int j;
  // TODO: fix implementation and loop annotations).
  /*@ loop invariant i < j <= n;
    @ loop assigns j;
    @ loop variant n-j;
    @*/
  for (j=i+1; j < n; j++) {
  }
 return 0;
}

// TODO: provide et prove a specification such that   
//       assertions after label "L:" below are themselves proved !
void swap(int *a, int *b) {
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

/* SPECIFICATIONS OF SORT
 
  Inspired by an example of Claude Marché.

 */

/* Swap two elements of indexes "i" et "j" in array "a" without
   assigning other elements -- between two control points "L1" et
   "L2" (labels) of the program.
*/
/*@ predicate Swap{L1,L2}(int *a, integer i, integer j) =
  @   \at(a[i],L1) == \at(a[j],L2) &&
  @   \at(a[j],L1) == \at(a[i],L2) &&
  @   \forall integer k; k != i && k != j
  @       ==> \at(a[k],L1) == \at(a[k],L2);
  @*/

/* Permutation in slice "l..h" of array "a" without assigning
   other elements -- between two control points "L1" et
   "L2" (labels) of the program.
*/
/*@ axiomatic MyPermutationTheory {
  @  predicate Permut{L1,L2}(int *a, integer l, integer h) ;
  @  axiom Permut_refl{L}:
  @   \forall int *a, integer l, h; Permut{L,L}(a, l, h) ;
  @  axiom Permut_sym{L1,L2}:
  @    \forall int *a, integer l, h;
  @      Permut{L1,L2}(a, l, h) ==> Permut{L2,L1}(a, l, h) ;
  @  axiom Permut_trans{L1,L2,L3}:
  @    \forall int *a, integer l, h;
  @      Permut{L1,L2}(a, l, h) && Permut{L2,L3}(a, l, h) ==>
  @        Permut{L1,L3}(a, l, h) ;
  @  axiom Permut_swap{L1,L2}:
  @    \forall int *a, integer l, h, i, j;
  @       l <= i <= h && l <= j <= h && Swap{L1,L2}(a, i, j) ==>
  @     Permut{L1,L2}(a, l, h) ;
  @ }
  @*/

/* To be a sorted array in slice "l..h".
*/
/*@ predicate Sorted(int *a, integer l, integer h) =
  @   \forall integer i; l < i <= h ==> a[i-1] <= a[i] ;
  @*/



/*@ requires \valid(t+(0..n-1));
  @ assigns t[0..n-1];
  @ ensures Sorted(t,0,n-1);
  @ ensures Permut{Pre,Here}(t,0,n-1);
  @*/
void min_sort(int t[], int n) {
  int i, m;
  // TODO: fix implementation et loop annotations.
  /*@ loop invariant 0 <= i && Permut{Pre,Here}(t,0,n-1);
    @ loop assigns i, t[0..n-1], m;
    @ loop variant n-i;
    @*/
  for (i=0; i<n-1; i++) {
    m=minimum(t,i,n);
  L: /* useful label for asserts below ! */
    swap(t+i,t+m);
    //@ assert Swap{L,Here}(t,i,m);
    //@ assert Permut{L,Here}(t,0,n-1);
  }
}


// MAIN with TEST of "min_sort"
#include "any.h"
#define N 5

int main() {
  int t[N];
  int i;
  for (i=0; i<N; i++) {
    t[i]=any();
  }
  min_sort(t,N);
  // TEST that the array is sorted ! No test for permutation !
  for (i=1; i<N; i++) {
    if (t[i-1]>t[i]) 
      return i; // ERROR !
  }
  return 0; // trié
}
