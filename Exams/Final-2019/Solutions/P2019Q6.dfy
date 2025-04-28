method {:axiom} SemiPartition( a: array<int>, i: int, k: int, j: int )
    modifies a
    requires 0 <= i <= k <= j <= a.Length
    ensures forall p,q | i <= p < k <= q < j :: a[p] <= a[q]
    ensures multiset(a[i..j]) == old(multiset(a[i..j]))
    ensures a[..i] == old(a[..i])
    ensures a[j..] == old(a[j..])

method Sort( a: array<int>, i: int, j: int )
    modifies a
    decreases j-i
    requires 0 <= i <= j <= a.Length
    ensures a[..i] == old(a[..i])
    ensures a[j..] == old(a[j..])
    ensures multiset(a[i..j]) == old(multiset(a[i..j]))
    ensures forall p,q | i <= p < q < j :: a[p] <= a[q]
{
    if j-i < 2 { return; }
    var k := i+(j-i)/2;
    SemiPartition(a,i,k,j);
    Sort(a,i,k);
    Sort(a,k,j);
    assume multiset(a[i..j]) == old(multiset(a[i..j]));
    assume forall p, q | i <= p < q < j :: a[p] <= a[q];
}