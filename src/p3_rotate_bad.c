#include <stddef.h>

/*@
  requires n > 0;
  requires \valid(a + (0 .. n-1));
  assigns a[0 .. n-1];
  ensures \forall integer i; 0 <= i < n - 1 ==> a[i] == \old(a[i + 1]);
  ensures a[n - 1] == \old(a[0]);
*/
void p3_rotate_left(int *a, int n) {
  int i = 0;
  while (i < n - 1) {
    a[i] = a[i + 1];
    i++;
  }
  /* BUG: forgets original first element; copies last-1 value instead */
  a[n - 1] = a[n - 2];
}
