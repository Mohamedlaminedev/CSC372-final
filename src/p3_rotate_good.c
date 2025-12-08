#include <stddef.h>

/*@
  requires n > 0;
  requires \valid(a + (0 .. n-1));
  assigns a[0 .. n-1];
  ensures \forall integer i; 0 <= i < n - 1 ==> a[i] == \old(a[i + 1]);
  ensures a[n - 1] == \old(a[0]);
*/
void p3_rotate_left(int *a, int n) {
  int first = a[0];
  int i = 0;
  /*@ loop invariant 0 <= i <= n - 1;
      loop invariant \\forall integer k; 0 <= k < i ==> a[k] == \\old(a[k + 1]);
      loop assigns i, a[0 .. n - 2];
      loop variant n - 1 - i;
  */
  while (i < n - 1) {
    a[i] = a[i + 1];
    i++;
  }
  a[n - 1] = first;
}
