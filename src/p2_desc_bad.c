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
  /* LLM will generate falsifying implementation here */
}
