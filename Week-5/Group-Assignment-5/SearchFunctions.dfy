// Seaarch Functions:

// a. Pic: C, Inv: 5
method Search( a: array, i: int, j: int, x: int ) returns ( k: int )
requires 0 <= i <= j <= a.Length;
requires forall p,q | i <= p < q < j :: a[p] <= a[q];
ensures i <= k < j || k == -1;
ensures i <= k < j ==> a[k] == x;
ensures k == -1 ==> !exists k | i <= k < j :: a[k] == x;

// b. Pic: D, Inv: 6
method Search( a: array, i: int, j: int, x: int ) returns ( k: int )
requires 0 <= i <= j <= a.Length;
requires forall p,q | i <= p < q < j :: a[p] >= a[q];
ensures i <= k <= j;
ensures forall p | i <= p < k :: a[p] > x;
ensures forall p | k <= p < j :: a[p] <= x;

// c. Pic: E, Inv: 1
method Search( a: array, i: int, j: int, x: int ) returns ( k: int )
requires 0 <= i <= j <= a.Length;
requires forall p,q | i <= p < q < j :: a[p] >= a[q];
ensures i <= k <= j;
ensures forall p | i <= p < k :: a[p] >= x;
ensures forall p | k <= p < j :: a[p] < x;

// d. Pic: F, Inv: 2
method Search( a: array, i: int, j: int, x: int ) returns ( k: int )
requires 0 <= i <= j <= a.Length;
requires forall p,q | i <= p < q < j :: a[p] >= a[q];
ensures i <= k < j || k == -1;
ensures i <= k < j ==> a[k] == x;
ensures k == -1 ==> !exists k | i <= k < j :: a[k] == x;

// e. Pic: A, Inv: 3
method Search( a: array, i: int, j: int, x: int ) returns ( k: int )
requires 0 <= i <= j <= a.Length;
requires forall p,q | i <= p < q < j :: a[p] <= a[q];
ensures i <= k <= j;
ensures forall p | i <= p < k :: a[p] < x;
ensures forall p | k <= p < j :: a[p] >= x;

// f. Pic: B, Inv: 4
method Search( a: array, i: int, j: int, x: int ) returns ( k: int )
requires 0 <= i <= j <= a.Length;
requires forall p,q | i <= p < q < j :: a[p] <= a[q];
ensures i <= k <= j;
ensures forall p | i <= p < k :: a[p] <= x;
ensures forall p | k <= p < j :: a[p] > x;

// Loop Invariants:

// 1. Pic: E, Fun: C
invariant i <= p <= q <= j;
invariant forall r | i <= r < p :: a[r] >= x;
invariant forall r | q <= r < j :: a[r] < x;

// 2. Pic: F, Fun: D
invariant i <= p <= q <= j;
invariant forall r | i <= r < p :: a[r] > x;
invariant forall r | q <= r < j :: a[r] < x;

// 3. Pic: A, Fun: E
invariant i <= p <= q <= j;
invariant forall r | i <= r < p :: a[r] < x;
invariant forall r | q <= r < j :: a[r] >= x;

// 4. Pic: B, Fun: F
invariant i <= p <= q <= j;
invariant forall r | i <= r < p :: a[r] <= x;
invariant forall r | q <= r < j :: a[r] > x;

// 5. Pic: C, Fun: A
invariant i <= p <= q <= j;
invariant forall r | i <= r < p :: a[r] < x;
invariant forall r | q <= r < j :: a[r] > x;

// 6. Pic: D, Fun: B
invariant i <= p <= q <= j;
invariant forall r | i <= r < p :: a[r] > x;
invariant forall r | q <= r < j :: a[r] <= x;