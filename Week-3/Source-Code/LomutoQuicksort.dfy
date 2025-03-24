include "QuicksortAxioms.dfy"

method LomutoQuicksort( a: array<int>, i: int, j: int )
	decreases j-i
	modifies a
	requires 0 <= i <= j <= a.Length
	ensures a[..i] == old(a[..i])
	ensures a[j..] == old(a[j..])
	ensures multiset(a[i..j]) == old(multiset(a[i..j]))
	ensures forall u,v | i <= u < v < j :: a[u] <= a[v]
{
	if j-i < 2 { return; }
	var p := a[i];
	var r := i+1;
	var s := r;
	ghost var original := a[..];
	while s != j
		decreases j-s
		invariant i < r <= s <= j
		invariant a[..i] == old(a[..i])
		invariant a[j..] == old(a[j..])
		invariant multiset(a[i..j]) == old(multiset(a[i..j]))
		invariant a[i] == p
		invariant forall u | i < u < r :: a[u] < p
		invariant forall u | r <= u < s :: a[u] >= p
	{
		// |p| <p | >=p | ??? |
		//  i      r     s     j
		if a[s] < p
		{
			a[r], a[s] := a[s], a[r];
			r := r+1;
		}
		s := s+1;
	}
	// |p| <p | >=p |
	//  i      r     s
	//               j
	r := r-1;
	a[i], a[r] := a[r], p;
	// | <p |p| >=p |
	//  i    r       s
	//               j
	ghost var partitioned := a[..];
	LomutoQuicksort(a,i,r);
	ghost var sortedonce := a[..];
	LomutoQuicksort(a,r+1,j);
	LemmaSinglePivotQuicksort(original,partitioned,sortedonce,a[..],i,r,r+1,j,p);
}
