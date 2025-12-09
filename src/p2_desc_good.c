#include <stddef.h>

/*@
  requires n >= 0;
  requires \valid(a + (0 .. n-1));
  requires \valid(desc);
  assigns *desc;
  ensures (*desc == 1) ==> (\forall integer i, j; 0 <= i < j < n ==> \old(a[i]) > \old(a[j]));
  ensures (*desc == 0) ==> (n <= 1 || (\exists integer i, j; 0 <= i < j < n && \old(a[i]) <= \old(a[j])));
*/
void p2_is_strictly_desc(const int *a, int n, int *desc) {
  if (n <= 1) {
    *desc = 1;
    return;
  }

  int strictly = 1;
  int i = 1;
  /*@ loop invariant 1 <= i <= n;
      loop invariant strictly == 1 ==>
        (\forall integer k; 1 <= k < i ==> a[k - 1] > a[k]);
      loop assigns i, strictly;
      loop variant n - i;
  */
  while (i < n && strictly) {
    if (a[i - 1] <= a[i]) {
      strictly = 0;
    }
    i++;
  }

  *desc = strictly;
}
