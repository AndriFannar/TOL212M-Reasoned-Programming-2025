include "QuicksortLemmas.dfy"

method Partition( a: array<int>, i: int, j: int ) returns ( p: int, q: int )
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
    p,q,r := i,i+1,j;
    while q != r
        // | <piv | =piv | ??? | >piv |
        //  i      p      q     r      j
        decreases r-q
        invariant i <= p < q <= r <= j
        invariant forall z | i <= z < p :: a[z] < a[p]
        invariant forall z | p <= z < q :: a[z] == piv
        invariant forall z | r <= z < j :: a[z] > a[p]
        invariant multiset(a[i..j]) == old(multiset(a[i..j]))
        invariant a[..i] == old(a[..i])
        invariant a[j..] == old(a[j..])
    {
        if a[q] < piv
        {
            a[p], a[q] := a[q], a[p];
            assert multiset(a[i..j]) == old(multiset(a[i..j]));
            p := p+1; q := q+1;
        }
        else if a[q] > piv
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

method Sort( a: array<int>, i: int, j: int )
    decreases j-i
    modifies a
    requires 0 <= i <= j <= a.Length
    ensures a[..i] == old(a[..i])
    ensures a[j..] == old(a[j..])
    ensures multiset(a[i..j]) == old(multiset(a[i..j]))
    ensures forall p,q | i <= p < q < j :: a[p] <= a[q]
{
    if j-i < 2 { return; }
    ghost var original := a[..];
    var p,q := Partition(a,i,j);
    var piv := a[p];
    assert forall r | p <= r < q :: a[r] == piv;
    ghost var partitioned := a[..];
    Sort(a,i,p);
    assert forall r | p <= r < q :: a[r] == piv;
    ghost var sortedonce := a[..];
    Sort(a,q,j);
    assert forall r | p <= r < q :: a[r] == piv;
    LemmaSinglePivotQuicksort(original,partitioned,sortedonce,a[..],i,p,q,j,piv);
}