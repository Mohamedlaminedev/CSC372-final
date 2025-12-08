#include <stddef.h>

/*@
  requires n >= 0;
  requires \valid(a + (0 .. n-1));
  assigns a[0 .. n-1];
  ensures \forall integer k; 0 <= k < n ==> ((\old(a[k]) <= 0 ==> a[k] == 0) && (\old(a[k]) > 0 ==> a[k] == k));
*/
void p4_transform(int *a, int n) {
  int k = 0;
  /*@ loop invariant 0 <= k <= n;
      loop invariant \\forall integer i; 0 <= i < k ==>
        ((\\at(a[i], Pre) <= 0 ==> a[i] == 0) &&
         (\\at(a[i], Pre) > 0 ==> a[i] == i));
      loop assigns k, a[0 .. n - 1];
      loop variant n - k;
  */
  while (k < n) {
    int original = a[k];
    if (original <= 0) {
      a[k] = 0;
    } else {
      a[k] = k;
    }
    k++;
  }
}
