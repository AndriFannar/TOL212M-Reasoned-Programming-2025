method Search( a: seq<int> ) returns( k: int )
    requires forall p, q | 0 <= p < q < |a| :: a[p] <= a[q]
    ensures -1 <= k < |a|
    ensures k == -1 ==> forall z | z in a :: z != 0
    ensures k >= 0 ==> forall r | 0 <= r < k :: a[r] < 0
{
    var p, q := 0, |a|;
    while p < q
        invariant 0 <= p <= q <= |a|
        decreases q-p
        invariant forall r | 0 <= r < p :: a[r] < 0
        invariant forall r | q <= r < |a| :: a[r] >= 0
    {
        var m := p+(q-p)/2;
        if a[m] < 0 { p := m+1; }
        else        { q := m;   }
    }
    if p == |a| { return -1; }
    if a[p] == 0 { return p; }
    return -1;
}