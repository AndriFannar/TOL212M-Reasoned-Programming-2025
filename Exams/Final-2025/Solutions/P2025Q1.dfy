method P2025Q1( a: seq<int> ) returns( k: int )
    requires forall p, q | 0 <= p < q < |a| :: a[p] <= a[q]
    ensures 0 <= k <= |a|
    ensures forall r | 0 <= r < k :: a[r] <= 2025
    ensures forall r | k <= r < |a| :: a[r] > 2025
{
    var p, q := 0, |a|;
    while p < q 
        decreases q-p
        invariant 0 <= p <= q <= |a|
        invariant forall r | 0 <= r < p :: a[r] <= 2025
        invariant forall r | q <= r < |a| :: a[r] > 2025
    {
        var m := p+(q-p)/2;
        if a[m] <= 2025 { p := m+1; }
        else           { q := m;   }
    }
    k := p;
}