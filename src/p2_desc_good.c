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
  int i = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant strictly == 1 ==>
        (\\forall integer p, q; 0 <= p < q < i ==> a[p] > a[q]);
      loop assigns i, strictly;
      loop variant n - i;
  */
  while (i < n && strictly) {
    int j = i + 1;
    /*@ loop invariant i + 1 <= j <= n;
        loop invariant strictly == 1 ==>
          (\\forall integer q; i < q < j ==> a[i] > a[q]);
        loop assigns j, strictly;
        loop variant n - j;
    */
    while (j < n && strictly) {
      if (a[i] <= a[j]) {
        strictly = 0;
      }
      j++;
    }
    i++;
  }

  *desc = strictly;
}
