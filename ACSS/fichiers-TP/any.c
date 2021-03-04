#include <stdio.h>
#include "any.h"

/* returns an integer from standard input */
int any() {
  static int count=1;
  int result, c ;
  printf("Enter integer num %d:", count);
  while (!scanf("%d",&result)) {
    while ((c=getchar()) != '\n' && c!=EOF) ; /* flush stdin */
    printf("invalid integer syntax !\n");
    printf("Please, enter again integer num %d:",count);
  }
  count++;
  return result;
}
