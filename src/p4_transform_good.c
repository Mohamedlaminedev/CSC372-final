#include <stddef.h>

/*@
  requires n >= 0;
  requires \valid(a + (0 .. n-1));
  assigns a[0 .. n-1];
  ensures \forall integer k; 0 <= k < n ==> ((\old(a[k]) <= 0 ==> a[k] == 0) && (\old(a[k]) > 0 ==> a[k] == k));
*/
void p4_transform(int *a, int n) {
  /* LLM will generate satisfying implementation here */
}
