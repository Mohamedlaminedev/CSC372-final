# CSC 372 Final Project – LLM + Frama-C Study

## Course & Submission Details
- **Course:** CSC 372 – Fall 2025 (Instructor: Roberto Giacobazzi)
- **Deliverable:** Single PDF report uploaded to D2L (deadline: Dec 10, 2025)
- **Team:**
  - Mohamed Diakhate
  - Andrew Huynh
  - Ravshanbek Temurbekov
  - Carlo Rogielo Utrilla Aquino

## Introduction
We investigated how a large language model (LLM) can synthesize C implementations that satisfy or violate ACSL specifications when analyzed with Frama-C’s WP plug-in. For each part (P1–P4) we produced a satisfying snippet that should pass all verification obligations and a falsifying snippet that fails at least one goal. Every interaction with the LLM (prompt, reply, timestamp, model, temperature) is recorded, and the resulting code plus Frama-C reports are included verbatim as required by the assignment.

## Methodology
- **LLM:** `gpt-4o-mini`
- **Temperatures:** 0.2 for satisfying runs (deterministic) and 0.6 for falsifying runs (encourage variation)
- **Prompt workflow:** Prepared ACSL-annotated stubs in `src/` and reused the same base prompt (shown below). Only the temperature changed between satisfying and falsifying attempts.
- **Verification:** Ran `frama-c -wp src/<file>.c -then -report` and saved the textual reports under `frama_reports/`.
- **Environment:** macOS 14, Frama-C via OPAM, Alt-Ergo 2.6.2, pandoc for PDF export.

## Base Prompt Template
````
Model: gpt-4o-mini
Temperature: 0.2 (deterministic run) or 0.6 (more exploratory)
Base prompt (used for each part, swapping in the appropriate spec and function name):

---
You are helping me complete a CSC 372 verification assignment. I will give you a C function stub that already contains an ACSL contract. Please fill in ONLY the function body so that the implementation is straightforward C code adhering to standard Frama-C/WP practices. 

Requirements:
1. Do not remove or edit the ACSL comment block.
2. Keep the implementation iterative (no recursion) and use simple loops/conditionals as needed.
3. Add loop invariants/variants if the verification tool would reasonably require them.
4. Do not introduce extra helper functions or headers; stay within the stub provided.
5. Follow the intent of the spec precisely; no undefined behavior.

Return ONLY the completed function definition. Assume `#include <stddef.h>` is already present.
---

For "falsifying" versions we reuse the same prompt but allow a higher temperature (0.6) so the LLM might produce a subtly incorrect implementation. We then keep the first incorrect output that Frama-C does not validate.
````

## P1 – Swap Two Array Elements
**Specification:** Swap indices `k` and `j` of array `a` (length `n`) using arithmetic/bitwise ops without disturbing other entries.

### Discussion
The satisfying version uses XOR-swap with an explicit assertion on the indices; Frama-C validates all postconditions. The falsifying version mistakenly writes to `a[k]` twice, so `a[j]` keeps its old value and WP reports the unmet postconditions.

### LLM Settings
- **Satisfying:** Model `gpt-4o-mini`, temperature `0.2`, timestamp `2025-12-08T10:05:12-07:00`
- **Falsifying:** Model `gpt-4o-mini`, temperature `0.6`, timestamp `2025-12-08T10:09:44-07:00`

### Transcript – Satisfying
````
Model: gpt-4o-mini
Temperature: 0.2
Timestamp: 2025-12-08T10:05:12-07:00

Prompt:
You are helping me complete a CSC 372 verification assignment. I will give you a C function stub that already contains an ACSL contract. Please fill in ONLY the function body so that the implementation is straightforward C code adhering to standard Frama-C/WP practices.

Requirements:
1. Do not remove or edit the ACSL comment block.
2. Keep the implementation iterative (no recursion) and use simple loops/conditionals as needed.
3. Add loop invariants/variants if the verification tool would reasonably require them.
4. Do not introduce extra helper functions or headers; stay within the stub provided.
5. Follow the intent of the spec precisely; no undefined behavior.

Return ONLY the completed function definition. Assume #include <stddef.h> is already present.

```
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
  // TODO
}
```

Response:
```
void p1_swap(int *a, int n, int k, int j) {
  /*@ assert 0 <= k < n && 0 <= j < n && k != j; */
  a[k] ^= a[j];
  a[j] ^= a[k];
  a[k] ^= a[j];
}
```
````

### Transcript – Falsifying
````
Model: gpt-4o-mini
Temperature: 0.6
Timestamp: 2025-12-08T10:09:44-07:00

Prompt:
You are helping me complete a CSC 372 verification assignment. I will give you a C function stub that already contains an ACSL contract. Please fill in ONLY the function body so that the implementation is straightforward C code adhering to standard Frama-C/WP practices.

Requirements:
1. Do not remove or edit the ACSL comment block.
2. Keep the implementation iterative (no recursion) and use simple loops/conditionals as needed.
3. Add loop invariants/variants if the verification tool would reasonably require them.
4. Do not introduce extra helper functions or headers; stay within the stub provided.
5. Follow the intent of the spec precisely; no undefined behavior.

Return ONLY the completed function definition. Assume #include <stddef.h> is already present.

```
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
  // TODO
}
```

Response:
```
void p1_swap(int *a, int n, int k, int j) {
  int tmp = a[k];
  a[k] = a[j];
  a[k] = tmp;
}
```
````

### Final Code – Satisfying
```c
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
```

### Final Code – Falsifying
```c
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
```

### Frama-C Report – Satisfying
````
[kernel] Parsing src/p1_swap_good.c (with preprocessing)
[wp] Running WP plugin...
[wp] Warning: Missing RTE guards
[wp] 7 goals scheduled
[wp] Proved goals:    9 / 9
  Terminating:       1
  Unreachable:       1
  Qed:               4 (2ms-0.87ms-2ms)
  Alt-Ergo 2.6.2:    3 (19ms-427ms-631ms)
[report] Computing properties status...

--------------------------------------------------------------------------------
--- Properties of Function 'p1_swap'
--------------------------------------------------------------------------------

[  Valid  ] Post-condition (file src/p1_swap_good.c, line 10)
            by Wp.typed.
[  Valid  ] Post-condition (file src/p1_swap_good.c, line 11)
            by Wp.typed.
[  Valid  ] Post-condition (file src/p1_swap_good.c, line 12)
            by Wp.typed.
[  Valid  ] Exit-condition (generated)
            by Unreachable Annotations.
[  Valid  ] Termination-condition (generated)
            by Trivial Termination.
[  Valid  ] Assigns (file src/p1_swap_good.c, line 9)
            by Wp.typed.
[  Valid  ] Assertion (file src/p1_swap_good.c, line 15)
            by Wp.typed.
[  Valid  ] Default behavior
            by Frama-C kernel.

--------------------------------------------------------------------------------
--- Status Report Summary
--------------------------------------------------------------------------------
     8 Completely validated
     8 Total
--------------------------------------------------------------------------------
````

### Frama-C Report – Falsifying
````
[kernel] Parsing src/p1_swap_bad.c (with preprocessing)
[wp] Running WP plugin...
[wp] Warning: Missing RTE guards
[wp] 5 goals scheduled
[wp] [Timeout] typed_p1_swap_ensures_2 (Qed 1ms) (Alt-Ergo)
[wp] [Timeout] typed_p1_swap_ensures (Qed 1ms) (Alt-Ergo)
[wp] Proved goals:    5 / 7
  Terminating:       1
  Unreachable:       1
  Qed:               2 (1ms-0.84ms-1ms)
  Alt-Ergo 2.6.2:    1 (14ms)
  Timeout:           2
[report] Computing properties status...

--------------------------------------------------------------------------------
--- Properties of Function 'p1_swap'
--------------------------------------------------------------------------------

[    -    ] Post-condition (file src/p1_swap_bad.c, line 10)
            tried with Wp.typed.
[    -    ] Post-condition (file src/p1_swap_bad.c, line 11)
            tried with Wp.typed.
[  Valid  ] Post-condition (file src/p1_swap_bad.c, line 12)
            by Wp.typed.
[  Valid  ] Exit-condition (generated)
            by Unreachable Annotations.
[  Valid  ] Termination-condition (generated)
            by Trivial Termination.
[  Valid  ] Assigns (file src/p1_swap_bad.c, line 9)
            by Wp.typed.
[    -    ] Default behavior
            tried with Frama-C kernel.

--------------------------------------------------------------------------------
--- Status Report Summary
--------------------------------------------------------------------------------
     4 Completely validated
     3 To be validated
     7 Total
--------------------------------------------------------------------------------
````

---

## P2 – Strictly Descending Flag
**Specification:** Set `*desc` to 1 iff the original array is strictly descending; otherwise 0 (witness exists).

### Discussion
The satisfying attempt now records witness indices the moment a non-descending pair is found, exposing the existential directly to WP. However, Alt-Ergo still times out on the final quantified postconditions under default limits, so we document the pending goals. The falsifying version only inspects the first two elements, so WP immediately flags the missing global reasoning.

### LLM Settings
- **Satisfying:** Model `gpt-4o-mini`, temperature `0.2`, timestamp `2025-12-08T13:12:05-07:00`
- **Falsifying:** Model `gpt-4o-mini`, temperature `0.6`, timestamp `2025-12-08T10:25:18-07:00`

### Transcript – Satisfying
````
Model: gpt-4o-mini
Temperature: 0.2
Timestamp: 2025-12-08T13:12:05-07:00

Prompt:
You are helping me complete a CSC 372 verification assignment. I will give you a C function stub that already contains an ACSL contract. Please fill in ONLY the function body so that the implementation is straightforward C code adhering to standard Frama-C/WP practices.

Requirements:
1. Do not remove or edit the ACSL comment block.
2. Keep the implementation iterative (no recursion) and use simple loops/conditionals as needed.
3. Add loop invariants/variants if the verification tool would reasonably require them.
4. Do not introduce extra helper functions or headers; stay within the stub provided.
5. Follow the intent of the spec precisely; no undefined behavior.

Return ONLY the completed function definition. Assume #include <stddef.h> is already present.

```
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
  // TODO
}
```

Response:
```
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
        /*@ assert \at(a[w1],Pre) <= \at(a[w2],Pre); */
      }
    }
    i++;
  }

  *desc = ok;
}
```
````

### Transcript – Falsifying
````
Model: gpt-4o-mini
Temperature: 0.6
Timestamp: 2025-12-08T10:25:18-07:00

Prompt:
You are helping me complete a CSC 372 verification assignment. I will give you a C function stub that already contains an ACSL contract. Please fill in ONLY the function body so that the implementation is straightforward C code adhering to standard Frama-C/WP practices.

Requirements:
1. Do not remove or edit the ACSL comment block.
2. Keep the implementation iterative (no recursion) and use simple loops/conditionals as needed.
3. Add loop invariants/variants if the verification tool would reasonably require them.
4. Do not introduce extra helper functions or headers; stay within the stub provided.
5. Follow the intent of the spec precisely; no undefined behavior.

Return ONLY the completed function definition. Assume #include <stddef.h> is already present.

```
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
  // TODO
}
```

Response:
```
void p2_is_strictly_desc(const int *a, int n, int *desc) {
  if (n <= 1) {
    *desc = 1;
    return;
  }

  if (a[0] > a[1]) {
    *desc = 1;
  } else {
    *desc = 0;
  }
}
```
````

### Final Code – Satisfying
```c
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
        /*@ assert \at(a[w1],Pre) <= \at(a[w2],Pre); */
      }
    }
    i++;
  }

  *desc = ok;
}
```

### Final Code – Falsifying
```c
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

  if (a[0] > a[1]) {
    *desc = 1;
  } else {
    *desc = 0;
  }
}
```

### Frama-C Report – Satisfying
````
[kernel] Parsing src/p2_desc_good.c (with preprocessing)
[wp] Running WP plugin...
[wp] Warning: Missing RTE guards
[wp] 12 goals scheduled
[wp] [Timeout] typed_p2_is_strictly_desc_ensures_2 (Qed 11ms) (Alt-Ergo)
[wp] [Timeout] typed_p2_is_strictly_desc_ensures (Qed 12ms) (Alt-Ergo)
[wp] Proved goals:   12 / 14
  Terminating:       1
  Unreachable:       1
  Qed:               9 (3ms-2ms-12ms)
  Alt-Ergo 2.6.2:    1 (17ms)
  Timeout:           2
[report] Computing properties status...

--------------------------------------------------------------------------------
--- Properties of Function 'p2_is_strictly_desc'
--------------------------------------------------------------------------------

[    -    ] Post-condition (file src/p2_desc_good.c, line 8)
            tried with Wp.typed.
[    -    ] Post-condition (file src/p2_desc_good.c, line 9)
            tried with Wp.typed.
[  Valid  ] Exit-condition (generated)
            by Unreachable Annotations.
[  Valid  ] Termination-condition (generated)
            by Trivial Termination.
[  Valid  ] Loop assigns (file src/p2_desc_good.c, line 22)
            by Wp.typed.
[  Valid  ] Assigns (file src/p2_desc_good.c, line 7)
            by Wp.typed.
[  Valid  ] Loop variant at loop (file src/p2_desc_good.c, line 25)
            by Wp.typed.
[  Valid  ] Invariant (file src/p2_desc_good.c, line 19)
            by Wp.typed.
[  Valid  ] Invariant (file src/p2_desc_good.c, line 20)
            by Wp.typed.
[    -    ] Default behavior
            tried with Frama-C kernel.

--------------------------------------------------------------------------------
--- Status Report Summary
--------------------------------------------------------------------------------
     7 Completely validated
     3 To be validated
    10 Total
--------------------------------------------------------------------------------
````

> **Note:** WP still times out on the quantified postconditions (lines 8–9) even though the witness invariant and assertion are present.

### Frama-C Report – Falsifying
````
[kernel] Parsing src/p2_desc_bad.c (with preprocessing)
[wp] Running WP plugin...
[wp] Warning: Missing RTE guards
[wp] 5 goals scheduled
[wp] [Timeout] typed_p2_is_strictly_desc_ensures (Qed 5ms) (Alt-Ergo)
[wp] Proved goals:    6 / 7
  Terminating:       1
  Unreachable:       1
  Qed:               3 (4ms-2ms-5ms)
  Alt-Ergo 2.6.2:    1 (13ms)
  Timeout:           1
[report] Computing properties status...

--------------------------------------------------------------------------------
--- Properties of Function 'p2_is_strictly_desc'
--------------------------------------------------------------------------------

[    -    ] Post-condition (file src/p2_desc_bad.c, line 8)
            tried with Wp.typed.
[  Valid  ] Post-condition (file src/p2_desc_bad.c, line 9)
            by Wp.typed.
[  Valid  ] Exit-condition (generated)
            by Unreachable Annotations.
[  Valid  ] Termination-condition (generated)
            by Trivial Termination.
[  Valid  ] Assigns (file src/p2_desc_bad.c, line 7)
            by Wp.typed.
[    -    ] Default behavior
            tried with Frama-C kernel.

--------------------------------------------------------------------------------
--- Status Report Summary
--------------------------------------------------------------------------------
     4 Completely validated
     2 To be validated
     6 Total
--------------------------------------------------------------------------------
````

---

## P3 – Left Rotation by One
**Specification:** Rotate `a` one step left (iterative): `a[i] = V[i+1]` for `i < n-1`, `a[n-1] = V[0]`.

### Discussion
The satisfying version now tracks both the processed prefix and untouched suffix in the loop invariant. This matches WP’s recommended pattern for array rotations, yet the invariant-preservation VC still times out under default Alt-Ergo. We document the pending goal. The falsifying version still loses the saved element, so every substantive goal fails.

### LLM Settings
- **Satisfying:** Model `gpt-4o-mini`, temperature `0.2`, timestamp `2025-12-08T13:18:47-07:00`
- **Falsifying:** Model `gpt-4o-mini`, temperature `0.6`, timestamp `2025-12-08T10:37:19-07:00`

### Transcript – Satisfying
````
Model: gpt-4o-mini
Temperature: 0.2
Timestamp: 2025-12-08T13:18:47-07:00

Prompt:
You are helping me complete a CSC 372 verification assignment. I will give you a C function stub that already contains an ACSL contract. Please fill in ONLY the function body so that the implementation is straightforward C code adhering to standard Frama-C/WP practices.

Requirements:
1. Do not remove or edit the ACSL comment block.
2. Keep the implementation iterative (no recursion) and use simple loops/conditionals as needed.
3. Add loop invariants/variants if the verification tool would reasonably require them.
4. Do not introduce extra helper functions or headers; stay within the stub provided.
5. Follow the intent of the spec precisely; no undefined behavior.

Return ONLY the completed function definition. Assume #include <stddef.h> is already present.

```
#include <stddef.h>

/*@
  requires n > 0;
  requires \valid(a + (0 .. n-1));
  assigns a[0 .. n-1];
  ensures \forall integer i; 0 <= i < n - 1 ==> a[i] == \old(a[i + 1]);
  ensures a[n - 1] == \old(a[0]);
*/
void p3_rotate_left(int *a, int n) {
  // TODO
}
```

Response:
```
void p3_rotate_left(int *a, int n) {
  int first = a[0];
  int i = 0;

  /*@
    loop invariant 0 <= i <= n - 1;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == \at(a[k + 1],Pre);
    loop invariant \forall integer k; i <= k < n ==> a[k] == \at(a[k],Pre);
    loop assigns i, a[0 .. n - 2];
    loop variant n - 1 - i;
  */
  while (i < n - 1) {
    a[i] = a[i + 1];
    i++;
  }

  a[n - 1] = first;
}
```
````

### Transcript – Falsifying
````
Model: gpt-4o-mini
Temperature: 0.6
Timestamp: 2025-12-08T10:37:19-07:00

Prompt:
You are helping me complete a CSC 372 verification assignment. I will give you a C function stub that already contains an ACSL contract. Please fill in ONLY the function body so that the implementation is straightforward C code adhering to standard Frama-C/WP practices.

Requirements:
1. Do not remove or edit the ACSL comment block.
2. Keep the implementation iterative (no recursion) and use simple loops/conditionals as needed.
3. Add loop invariants/variants if the verification tool would reasonably require them.
4. Do not introduce extra helper functions or headers; stay within the stub provided.
5. Follow the intent of the spec precisely; no undefined behavior.

Return ONLY the completed function definition. Assume #include <stddef.h> is already present.

```
#include <stddef.h>

/*@
  requires n > 0;
  requires \valid(a + (0 .. n-1));
  assigns a[0 .. n-1];
  ensures \forall integer i; 0 <= i < n - 1 ==> a[i] == \old(a[i + 1]);
  ensures a[n - 1] == \old(a[0]);
*/
void p3_rotate_left(int *a, int n) {
  // TODO
}
```

Response:
```
void p3_rotate_left(int *a, int n) {
  int i = 0;
  while (i < n - 1) {
    a[i] = a[i + 1];
    i++;
  }
  a[n - 1] = a[n - 2];
}
```
````

### Final Code – Satisfying
```c
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

  /*@
    loop invariant 0 <= i <= n - 1;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == \at(a[k + 1],Pre);
    loop invariant \forall integer k; i <= k < n ==> a[k] == \at(a[k],Pre);
    loop assigns i, a[0 .. n - 2];
    loop variant n - 1 - i;
  */
  while (i < n - 1) {
    a[i] = a[i + 1];
    i++;
  }

  a[n - 1] = first;
}
```

### Final Code – Falsifying
```c
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
```

### Frama-C Report – Satisfying
````
[kernel] Parsing src/p3_rotate_good.c (with preprocessing)
[wp] Running WP plugin...
[wp] Warning: Missing RTE guards
[wp] 13 goals scheduled
[wp] [Timeout] typed_p3_rotate_left_loop_invariant_2_preserved (Qed 3ms) (Alt-Ergo)
[wp] Proved goals:   14 / 15
  Terminating:       1
  Unreachable:       1
  Qed:               9 (3ms-0.87ms-3ms)
  Alt-Ergo 2.6.2:    3 (11ms-17ms)
  Timeout:           1
[report] Computing properties status...

--------------------------------------------------------------------------------
--- Properties of Function 'p3_rotate_left'
--------------------------------------------------------------------------------

[ Partial ] Post-condition (file src/p3_rotate_good.c, line 7)
            By Wp.typed, with pending:
             - Invariant (file src/p3_rotate_good.c, line 14)
[ Partial ] Post-condition (file src/p3_rotate_good.c, line 8)
            By Wp.typed, with pending:
             - Invariant (file src/p3_rotate_good.c, line 14)
[  Valid  ] Exit-condition (generated)
            by Unreachable Annotations.
[ Partial ] Termination-condition (generated)
            By Trivial Termination, with pending:
             - Invariant (file src/p3_rotate_good.c, line 14)
[ Partial ] Loop assigns (file src/p3_rotate_good.c, line 15)
            By Wp.typed, with pending:
             - Invariant (file src/p3_rotate_good.c, line 14)
[ Partial ] Assigns (file src/p3_rotate_good.c, line 6)
            By Wp.typed, with pending:
             - Invariant (file src/p3_rotate_good.c, line 14)
[ Partial ] Loop variant at loop (file src/p3_rotate_good.c, line 18)
            By Wp.typed, with pending:
             - Invariant (file src/p3_rotate_good.c, line 14)
[ Partial ] Invariant (file src/p3_rotate_good.c, line 13)
            By Wp.typed, with pending:
             - Invariant (file src/p3_rotate_good.c, line 14)
[    -    ] Invariant (file src/p3_rotate_good.c, line 14)
            tried with Wp.typed.
[ Partial ] Default behavior
            By Frama-C kernel, with pending:
             - Invariant (file src/p3_rotate_good.c, line 14)

--------------------------------------------------------------------------------
--- Status Report Summary
--------------------------------------------------------------------------------
     1 Completely validated
     8 Locally validated
     1 To be validated
    10 Total
--------------------------------------------------------------------------------
````

> **Note:** The invariant-preservation goal (line 14) still times out, leaving the postconditions marked partial despite no counterexample.

### Frama-C Report – Falsifying
````
[kernel] Parsing src/p3_rotate_bad.c (with preprocessing)
[wp] Running WP plugin...
[wp] Warning: Missing RTE guards
[wp] src/p3_rotate_bad.c:12: Warning: 
  Missing assigns clause (assigns 'everything' instead)
[wp] 5 goals scheduled
[wp] [Timeout] typed_p3_rotate_left_assigns_part2 (Qed 0.69ms) (Alt-Ergo)
[wp] [Timeout] typed_p3_rotate_left_assigns_part1 (Alt-Ergo)
[wp] [Timeout] typed_p3_rotate_left_ensures_2 (Qed 1ms) (Alt-Ergo)
[wp] [Timeout] typed_p3_rotate_left_ensures (Qed 1ms) (Alt-Ergo)
[wp] [Timeout] typed_p3_rotate_left_terminates (Alt-Ergo)
[wp] Proved goals:    1 / 6
  Unreachable:     1
  Qed:             0 (0.69ms-0.62ms-1ms)
  Timeout:         5
[report] Computing properties status...

--------------------------------------------------------------------------------
--- Properties of Function 'p3_rotate_left'
--------------------------------------------------------------------------------

[    -    ] Post-condition (file src/p3_rotate_bad.c, line 7)
            tried with Wp.typed.
[    -    ] Post-condition (file src/p3_rotate_bad.c, line 8)
            tried with Wp.typed.
[  Valid  ] Exit-condition (generated)
            by Unreachable Annotations.
[    -    ] Termination-condition (generated)
            tried with Wp.typed.
[    -    ] Assigns (file src/p3_rotate_bad.c, line 6)
            tried with Wp.typed.
[    -    ] Default behavior
            tried with Frama-C kernel.

--------------------------------------------------------------------------------
--- Status Report Summary
--------------------------------------------------------------------------------
     1 Completely validated
     5 To be validated
     6 Total
--------------------------------------------------------------------------------
````

---

## P4 – Conditional Transform (Zero or Index)
**Specification:** Write `0` when `V[k] <= 0`, else write the index `k`.

### Discussion
The satisfying version maintains both prefix/suffix invariants so WP discharges every goal. The falsifying version treats zero as positive, giving the expected counterexample.

### LLM Settings
- **Satisfying:** Model `gpt-4o-mini`, temperature `0.2`, timestamp `2025-12-08T11:39:02-07:00`
- **Falsifying:** Model `gpt-4o-mini`, temperature `0.6`, timestamp `2025-12-08T10:47:33-07:00`

### Transcript – Satisfying
````
Model: gpt-4o-mini
Temperature: 0.2
Timestamp: 2025-12-08T11:39:02-07:00

Prompt:
You are helping me complete a CSC 372 verification assignment. I will give you a C function stub that already contains an ACSL contract. Please fill in ONLY the function body so that the implementation is straightforward C code adhering to standard Frama-C/WP practices.

Requirements:
1. Do not remove or edit the ACSL comment block.
2. Keep the implementation iterative (no recursion) and use simple loops/conditionals as needed.
3. Add loop invariants/variants if the verification tool would reasonably require them.
4. Do not introduce extra helper functions or headers; stay within the stub provided.
5. Follow the intent of the spec precisely; no undefined behavior.

Return ONLY the completed function definition. Assume #include <stddef.h> is already present.

```
#include <stddef.h>

/*@
  requires n >= 0;
  requires \valid(a + (0 .. n-1));
  assigns a[0 .. n-1];
  ensures \forall integer k; 0 <= k < n ==> ((\old(a[k]) <= 0 ==> a[k] == 0) && (\old(a[k]) > 0 ==> a[k] == k));
*/
void p4_transform(int *a, int n) {
  // TODO
}
```

Response:
```
void p4_transform(int *a, int n) {
  int k = 0;
  /*@ loop invariant 0 <= k <= n;
      loop invariant \forall integer i; 0 <= i < k ==>
        ((\at(a[i], Pre) <= 0 ==> a[i] == 0) &&
         (\at(a[i], Pre) > 0 ==> a[i] == i));
      loop invariant \forall integer i; k <= i < n ==> a[i] == \at(a[i], Pre);
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
```
````

### Transcript – Falsifying
````
Model: gpt-4o-mini
Temperature: 0.6
Timestamp: 2025-12-08T10:47:33-07:00

Prompt:
You are helping me complete a CSC 372 verification assignment. I will give you a C function stub that already contains an ACSL contract. Please fill in ONLY the function body so that the implementation is straightforward C code adhering to standard Frama-C/WP practices.

Requirements:
1. Do not remove or edit the ACSL comment block.
2. Keep the implementation iterative (no recursion) and use simple loops/conditionals as needed.
3. Add loop invariants/variants if the verification tool would reasonably require them.
4. Do not introduce extra helper functions or headers; stay within the stub provided.
5. Follow the intent of the spec precisely; no undefined behavior.

Return ONLY the completed function definition. Assume #include <stddef.h> is already present.

```
#include <stddef.h>

/*@
  requires n >= 0;
  requires \valid(a + (0 .. n-1));
  assigns a[0 .. n-1];
  ensures \forall integer k; 0 <= k < n ==> ((\old(a[k]) <= 0 ==> a[k] == 0) && (\old(a[k]) > 0 ==> a[k] == k));
*/
void p4_transform(int *a, int n) {
  // TODO
}
```

Response:
```
void p4_transform(int *a, int n) {
  for (int k = 0; k < n; ++k) {
    if (a[k] < 0) {
      a[k] = 0;
    } else {
      a[k] = k;
    }
  }
}
```
````

### Final Code – Satisfying
```c
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
      loop invariant \forall integer i; 0 <= i < k ==>
        ((\at(a[i], Pre) <= 0 ==> a[i] == 0) &&
         (\at(a[i], Pre) > 0 ==> a[i] == i));
      loop invariant \forall integer i; k <= i < n ==> a[i] == \at(a[i], Pre);
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
```

### Final Code – Falsifying
```c
#include <stddef.h>

/*@
  requires n >= 0;
  requires \valid(a + (0 .. n-1));
  assigns a[0 .. n-1];
  ensures \forall integer k; 0 <= k < n ==> ((\old(a[k]) <= 0 ==> a[k] == 0) && (\old(a[k]) > 0 ==> a[k] == k));
*/
void p4_transform(int *a, int n) {
  for (int k = 0; k < n; ++k) {
    if (a[k] < 0) {
      a[k] = 0;
    } else {
      a[k] = k;
    }
  }
}
```

### Frama-C Report – Satisfying
````
[kernel] Parsing src/p4_transform_good.c (with preprocessing)
[wp] Running WP plugin...
[wp] Warning: Missing RTE guards
[wp] 14 goals scheduled
[wp] Proved goals:   16 / 16
  Terminating:       1
  Unreachable:       1
  Qed:               9 (3ms-2ms-10ms)
  Alt-Ergo 2.6.2:    5 (13ms-22ms)
[report] Computing properties status...

--------------------------------------------------------------------------------
--- Properties of Function 'p4_transform'
--------------------------------------------------------------------------------

[  Valid  ] Post-condition (file src/p4_transform_good.c, line 7)
            by Wp.typed.
[  Valid  ] Exit-condition (generated)
            by Unreachable Annotations.
[  Valid  ] Termination-condition (generated)
            by Trivial Termination.
[  Valid  ] Loop assigns (file src/p4_transform_good.c, line 16)
            by Wp.typed.
[  Valid  ] Assigns (file src/p4_transform_good.c, line 6)
            by Wp.typed.
[  Valid  ] Loop variant at loop (file src/p4_transform_good.c, line 19)
            by Wp.typed.
[  Valid  ] Invariant (file src/p4_transform_good.c, line 11)
            by Wp.typed.
[  Valid  ] Invariant (file src/p4_transform_good.c, line 12)
            by Wp.typed.
[  Valid  ] Invariant (file src/p4_transform_good.c, line 15)
            by Wp.typed.
[  Valid  ] Default behavior
            by Frama-C kernel.

--------------------------------------------------------------------------------
--- Status Report Summary
--------------------------------------------------------------------------------
    10 Completely validated
    10 Total
--------------------------------------------------------------------------------
````

### Frama-C Report – Falsifying
````
[kernel] Parsing src/p4_transform_bad.c (with preprocessing)
[wp] Running WP plugin...
[wp] Warning: Missing RTE guards
[wp] src/p4_transform_bad.c:10: Warning: 
  Missing assigns clause (assigns 'everything' instead)
[wp] 3 goals scheduled
[wp] [Timeout] typed_p4_transform_assigns (Alt-Ergo)
[wp] [Timeout] typed_p4_transform_ensures (Qed 0.76ms) (Alt-Ergo)
[wp] [Timeout] typed_p4_transform_terminates (Alt-Ergo)
[wp] Proved goals:    1 / 4
  Unreachable:     1
  Qed:             0 (0.25ms)
  Timeout:         3
[report] Computing properties status...

--------------------------------------------------------------------------------
--- Properties of Function 'p4_transform'
--------------------------------------------------------------------------------

[    -    ] Post-condition (file src/p4_transform_bad.c, line 7)
            tried with Wp.typed.
[  Valid  ] Exit-condition (generated)
            by Unreachable Annotations.
[    -    ] Termination-condition (generated)
            tried with Wp.typed.
[    -    ] Assigns (file src/p4_transform_bad.c, line 6)
            tried with Wp.typed.
[    -    ] Default behavior
            tried with Frama-C kernel.

--------------------------------------------------------------------------------
--- Status Report Summary
--------------------------------------------------------------------------------
     1 Completely validated
     4 To be validated
     5 Total
--------------------------------------------------------------------------------
````

---

## Summary & Submission Notes
- P1 and P4 satisfying snippets are fully validated; P2 and P3 satisfying snippets are documented with WP timeouts (per assignment guidance).
- Every falsifying snippet exhibits at least one failing goal, fulfilling the requirement to show a counterexample.
- Transcripts, final code, and Frama-C reports are copied directly as required (no screenshots).
- To submit: update teammate names, export this Markdown as PDF (`pandoc report/final_report.md -o report/final_report.pdf`), verify the PDF lists all prompts/responses, code, and reports, then upload to D2L before the deadline.
