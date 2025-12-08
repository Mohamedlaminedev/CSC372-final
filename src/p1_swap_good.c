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
  /*@ assert 0 <= k < n && 0 <= j < n && k != j; */
  /* simple XOR-swap keeps everything else untouched */
  a[k] ^= a[j];
  a[j] ^= a[k];
  a[k] ^= a[j];
}
