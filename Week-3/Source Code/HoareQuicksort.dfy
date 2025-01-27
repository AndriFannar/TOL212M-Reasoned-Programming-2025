// Author: Snorri Agnarsson.

include "QuicksortAxioms.dfy"

// You can eiter use the above include or you
// can compile with:
//   dafny build HoareQuicksort.dfy --library QuicksortLemmas.doo
// The latter method uses the already compiled library resulting
// from QuicksortLemmas.dfy.

method HoareQuicksort( a: array<int>, i: int, j: int )
	decreases j-i
	modifies a
	requires 0 <= i <= j <= a.Length
	ensures a[..i] == old(a[..i])
	ensures a[j..] == old(a[j..])
	ensures multiset(a[i..j]) == old(multiset(a[i..j]))
	ensures forall u,v | i <= u < v < j :: a[u] <= a[v]
{
    if j-i < 2 {return;}
    var p := a[i+(j-i)/2];
    var r := i;
    var s := j;
    ghost var original := a[..];
    while r < s
		// | <=p | ??? | >=p |
		//  i     r     s     j
		decreases s-r
		invariant a[..i] == old(a[..i])
		invariant a[j..] == old(a[j..])
		invariant multiset(a[i..j]) == multiset(original[i..j])
		invariant multiset(a[i..j]) == old(multiset(a[i..j]))
		invariant i <= r <= j
		invariant i <= s <= j
		invariant r <= s+1
		invariant forall u | i <= u < r :: a[u] <= p
		invariant forall u | s <= u < j :: a[u] >= p
		invariant r > i ==> a[r-1] <= p
		invariant s < j ==> a[s] >= p
		invariant (s==j && r==i) ==> a[r+(s-r)/2]==p
		invariant (s==j && r>i) ==> exists u | r-1 <= u < s :: a[u] == p
		invariant r==i ==> exists u | r <= u < s :: a[u] == p
		invariant (i==r && s==j) || (i < r && s < j)
	{
		// | <=p | ??? | >=p |
		//  i     r     s     j
        while a[r] < p
			decreases s-r
			invariant a[..i] == old(a[..i])
			invariant a[j..] == old(a[j..])
			invariant multiset(a[i..j])
						== old(multiset(a[i..j]))
						== multiset(original[i..j])
			invariant i <= r <= j
			invariant i <= s <= j
			invariant r <= s+1
			invariant forall u | i <= u < r :: a[u] <= p
			invariant forall u | s <= u < j :: a[u] >= p
			invariant r > i ==> exists u | r-1 <= u < s :: a[u] <= p
			invariant s < j ==> exists u | r <= u <= s :: a[u] >= p
			invariant r > i ==> a[r-1] <= p
			invariant s < j ==> a[s] >= p
			invariant s == j ==> a[i+(j-i)/2] == p
			invariant s == j ==> r <= i+(j-i)/2
			invariant r == i ==> a[i+(j-i)/2] == p
			invariant r == i ==> s > i+(j-i)/2
			invariant r == i ==> exists u | r <= u < s :: a[u] == p
			invariant r <= s
		{
            r := r+1;
		}
        while a[s-1] > p
			decreases s-r
			invariant a[..i] == old(a[..i])
			invariant a[j..] == old(a[j..])
			invariant multiset(a[i..j])
						== old(multiset(a[i..j]))
						== multiset(original[i..j])
			invariant i <= r <= j
			invariant i <= s <= j
			invariant r <= s+1
			invariant forall u | i <= u < r :: a[u] <= p
			invariant forall u | s <= u < j :: a[u] >= p
			invariant r > i ==> exists u | r-1 <= u < s :: a[u] <= p
			invariant s < j ==> exists u | r <= u <= s :: a[u] >= p
			invariant r > i ==> a[r-1] <= p
			invariant s < j ==> a[s] >= p
			invariant s == j ==> a[i+(j-i)/2] == p
			invariant s == j ==> r <= i+(j-i)/2
			invariant r == i ==> a[i+(j-i)/2] == p
			invariant r == i ==> s > i+(j-i)/2
			invariant r <= s
		{
            s := s-1;
		}
        if r < s
        {
			s := s-1;
			Swap(a,i,r,s,j);
			r := r+1;
        }
	}
    // | <=p | =p | >=p |
    //  i     s    r     j
    ghost var partitioned := a[..];
    HoareQuicksort(a,i,s);
    ghost var sortedonce := a[..];
    HoareQuicksort(a,r,j);
    LemmaSinglePivotQuicksort   ( original
								, partitioned
								, sortedonce
								, a[..]
								, i
								, s
								, r
								, j
								, p
								);
}