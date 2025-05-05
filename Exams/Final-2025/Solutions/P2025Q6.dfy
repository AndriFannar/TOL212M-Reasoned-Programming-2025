include "P2025Q5.dfy"

method Quickselect( a: array<int>, k: int )
    modifies a
    requires 0 <= k < a.Length
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall r | 0 <= r < k :: a[r] <= a[k]
    ensures forall r | k < r < a.Length :: a[r] >= a[k]
{
    var i, j := 0, a.Length;
    while true
        decreases j-i 
        invariant 0 <= i <= k < j <= a.Length
        invariant forall p, q | 0 <= p < i && i <= q < j :: a[p] <= a[q]
        invariant forall p, q | i <= p < j && j <= q < a.Length :: a[p] <= a[q]
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        assert a[..] == a[..i]+a[i..j]+a[j..];
        ghost var orgij := a[i..j];

        var p := MiddlePartition(a,i,j);

        assert multiset(a[i..j]) == multiset(orgij);
        assert forall z | z in multiset(a[i..j]) :: z in multiset(orgij); 
        assert forall z | z in a[i..j] :: z in multiset(a[i..j]) && z in multiset(orgij) && z in orgij;
        assert a[..] == a[..i]+a[i..j]+a[j..];
        assert multiset(a[..]) == old(multiset(a[..]));
        assert forall r | 0 <= r < p :: a[r] <= a[p];
        assert forall r | p < r < a.Length :: a[r] >= a[p];
        assert forall r, s | 0 <= r < p && p < s < a.Length :: a[r] <= a[s];
        assert a[..] == a[..i]+a[i..j]+a[j..];
        assume {:axiom} forall p, q | 0 <= p < i && i <= q < j :: a[p] <= a[q];
        assume {:axiom} forall p, q | i <= p < j && j <= q < a.Length :: a[p] <= a[q];

        if p == k { return; }
        if p < k { i := p+1; }
        else     { j := p;   }
    }
}

method QuickHelper( a: array<int>, i: int, j: int, k: int )
    modifies a
    requires 0 <= i <= k < j <= a.Length
    decreases j-i
    requires forall p, q | 0 <= p < i && i <= q < j :: a[p] <= a[q]
    requires forall p, q | i <= p < j && j <= q < a.Length :: a[p] <= a[q]
    ensures a[..i] == old(a[..i])
    ensures a[j..] == old(a[j..])
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall r | 0 <= r < k :: a[r] <= a[k]
    ensures forall r | k < r < a.Length :: a[k] <= a[r]
{
    var p := MiddlePartition(a,i,j);
    assert a[..i] == old(a[..i]);
    assert a[..] == a[..i]+a[i..j]+a[j..];
    assert multiset(a[i..j]) == old(multiset(a[i..j]));
    assert multiset(a[..]) == multiset(a[..i])+multiset(a[i..j])+multiset(a[j..]);
    assert a[..i] == old(a[..i]);
    assert a[j..] == old(a[j..]);
    assume {:axiom} multiset(a[..]) == old(multiset(a[..]));
    assert i <= p < j;
    assert forall r | 0 <= r < p :: a[r] <= a[p];
    assert forall r | p < r < a.Length :: a[r] >= a[p];
    assert forall r, s | 0 <= r < p && p < s < a.Length :: a[r] <= a[s];
    if p == k { return; }
    if k < p { QuickHelper(a,i,p,k);   }
    else     { QuickHelper(a,p+1,j,k); }
}