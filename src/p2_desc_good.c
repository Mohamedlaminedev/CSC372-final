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

  int i = 1;
  int ok = 1;
  int w1 = 0;
  int w2 = 0;

  /*@
    loop invariant 1 <= i <= n;
    loop invariant ok == 1 ==> (\forall integer p, q; 0 <= p < q < i ==> \at(a[p],Pre) > \at(a[q],Pre));
    loop invariant ok == 0 ==> (\exists integer p, q; 0 <= p < q < i && \at(a[p],Pre) <= \at(a[q],Pre));
    loop assigns i, ok, w1, w2;
    loop variant n - i;
  */
  while (i < n) {
    if (ok) {
      if (a[i - 1] <= a[i]) {
        w1 = i - 1;
        w2 = i;
        ok = 0;
        /*@ assert \at(a[\at(w1,Here)],Pre) <= \at(a[\at(w2,Here)],Pre); */
      }
    }
    i++;
  }

  *desc = ok;
}
