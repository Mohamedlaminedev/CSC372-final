#include <stddef.h>

/*@
  requires n > 1;
  requires 0 <= k < n;
  requires 0 <= j < n;
  requires k != j;
  requires \valid(a + (0 .. n-1));
  assigns a[k], a[j];
  ensures a[k] == \old(a[j]);
  ensures a[j] == \old(a[k]);
  ensures \forall integer i; 0 <= i < n && i != k && i != j ==> a[i] == \old(a[i]);
*/
void p1_swap(int *a, int n, int k, int j) {
  int tmp = a[k];
  a[k] = a[j];
  /* BUG: second assignment writes back into a[k] again */
  a[k] = tmp;
}
