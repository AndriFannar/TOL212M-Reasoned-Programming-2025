// Q1
// Write a method in Dafny that searches with Binary Search in an integer
// sequence a, which is in ascending order, for the last position that
// contains a value < 100. If no such position exists then return -1.

method BinarySearchQ1 ( a: seq<int> ) returns ( k: int )
  decreases |a|
  requires forall p,q | 0 <= p <= q < |a| :: a[p] < a[q]
  ensures -1 <= k < |a|
  ensures k == -1 ==> forall p | p in a :: p >= 100
  ensures k != -1 ==> a[k] < 100
{
  // VERIFIED
  if ( a == [] ) { return -1; }
  var m := |a|/2;
  if ( a[m] < 100 )
  {
    k := BinarySearchQ1(a[m+1..]);
    if ( k == -1 ) { k := m; }
    else 					 { k := m+k+1; }
  }
  else { k := BinarySearchQ1(a[..m]); }
}

// Q2
// Write a recursive method in Dafny that searches an area with Binary Search
// in an integer sequence, which is in decreasing order, for the first position
// that contains a value < 100. If no such position exists then return -1.

method BinarySearchQ2 ( a: seq<int>, b: int, c: int ) returns ( k: int )
  decreases c-b
  requires 0 <= b <= c <= |a|
  requires forall p,q | b <= p < q < c :: a[p] >= a[q]
  ensures k == -1 ==> forall p | b <= p < c :: a[p] >= 100
  ensures k != -1 ==> ( b <= k < c ) &&
                      ( forall p | b <= p < k :: a[p] >= 100 ) &&
                      ( forall p | k <= p < c :: a[p] < 100 )
{
  // VERIFIED
  if ( b == c ) { return -1; }
  var m := b+(c-b)/2;
  if ( a[m] < 100 )
  {
    k := BinarySearchQ2(a, b, m);
    if ( k == -1 ) { k := m; }
  }
  else
  {
    k := BinarySearchQ2(a, m+1, c);
  }
}

// Q4
// Assume a Dafny function with the following description:
//
//	method Partition ( a: array<int>, i: int, j: int )
//			returns ( p: int, q: int )
//		modifies a
//		requires 0 <= i < j <= a.Length
//		ensures i <= p < q <= j
//		ensures forall r | i <= r < p :: a[r] < a[p]
//		ensures forall r | p <= r < q :: a[r] == a[p]
//		ensures forall r | q <= r < j :: a[r] > a[p]
//		ensures multiset(a[i..j]) == old(multiset(a[i..j]))
//		ensures a[..i] == old(a[..i])
//		ensures a[j..] == old(a[j..])
//
// Write a Quicksort function that uses this function as a helper
// function to transform a multiset into a sorted sequence of the
// same values. Do not program the Partition function here.

method QuicksortQ4 ( a: array<int>, i: int, j: int )
  decreases j-i
  modifies a
  requires 0 <= i < j <= a.Length
  ensures multiset(a[i..j]) == old(multiset(a[i..j]))
  ensures a[..i] == old(a[..i])
  ensures a[j..] == old(a[j..])
  ensures forall p,q | i <= p <= q < j :: a[p] <= a[q]
{
  if ( j-i < 2 ) { return; }
  var p, q := Partition(a, i, j);
  QuicksortQ4(a, i, p);
  QuicksortQ4(a, q, j);
}

// Q5
// Program the Partition function described above. Remember
// that all loops need an invariant.

method Partition ( a: array<int>, i: int, j: int )
		returns ( p: int, q: int )
	modifies a
	requires 0 <= i < j <= a.Length
	ensures i <= p < q <= j
	ensures forall r | i <= r < p :: a[r] < a[p]
	ensures forall r | p <= r < q :: a[r] == a[p]
	ensures forall r | q <= r < j :: a[r] > a[p]
	ensures multiset(a[i..j]) == old(multiset(a[i..j]))
	ensures a[..i] == old(a[..i])
	ensures a[j..] == old(a[j..])
{
  var r: int;
	var piv := a[i];
  p, q, r := i, i+1, j;
  while q != r
    decreases r-q
    invariant i <= p < q <= r <= j
    invariant forall z | i <= z < p :: a[z] < a[p]
    invariant forall z | p <= z < q :: a[z] == piv
    invariant forall z | r <= z < j :: a[z] > a[p]
    invariant multiset(a[i..j]) == old(multiset(a[i..j]))
    invariant a[..i] == old(a[..i])
    invariant a[j..] == old(a[j..])
  {
    if ( a[q] < piv ) 
    { 
      a[p], a[q] := a[q], a[p];
      assert multiset(a[i..j]) == old(multiset(a[i..j]));
      p := p+1;
      q := q+1;
    }
    else if ( a[q] > piv )
    {
      r := r-1;
      a[q], a[r] := a[r], a[q];
      assert multiset(a[i..j]) == old(multiset(a[i..j]));
    }
    else
    {
      q := q+1;
      assert multiset(a[i..j]) == old(multiset(a[i..j]));
    }
  }
}