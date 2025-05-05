include "QuicksortAxioms.dfy"
include "P2025Q5.dfy"

method Sort( a: array<int>, i: int, j: int )
    modifies a
    requires 0 <= i <= j <= a.Length
    decreases j-i
    ensures a[..i] == old(a[..i])
    ensures a[j..] == old(a[j..])
    ensures multiset(a[i..j]) == old(multiset(a[i..j]))
    ensures forall p, q | i <= p < q < j :: a[p] <= a[q]
{
    if j-i < 2 { return; }
	ghost var original := a[..];
    var k := MiddlePartition(a,i,j);
	ghost var partitioned := a[..];
    Sort(a,i,k);
	ghost var sortedonce := a[..];
    Sort(a,k+1,j);
    LemmaSinglePivotQuicksort(original,partitioned,sortedonce,a[..],i,k,k+1,j,a[k]);
}