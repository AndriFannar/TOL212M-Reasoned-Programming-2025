// Usage: k := BinarySearchFirstGE(a,x);
// Pre:   a is a seq<int> in ascending order, x is an int.
// Post:  0 <= k <= |a|, and all values in a[..k] are < x
//        and all values in a[k..] are >= x.
//
//        So the following figure is true
//
//        a: |  < x  |  >= x  |
//            ^       ^        ^
//            0       k       |a|
//
method BinarySearchFirstGE( a: seq<int>, x: int ) returns( k: int )
    requires forall p,q | 0 <= p < q < |a| :: a[p] <= a[q]
    ensures 0 <= k <= |a|
    ensures forall u | 0 <= u < k :: a[u] < x
    ensures forall u | k <= u < |a| :: a[u] >= x
{
    // Looping solution
    var p, q := 0, |a|;
    while p < q
        invariant 0 <= p <= q <= |a|
        invariant forall u | 0 <= u < p :: a[u] < x
        invariant forall u | q <= u < |a| :: a[u] >= x

        // a: |  < x  | ??? |  >= x  |
        //     ^       ^     ^        ^
        //     0       p     q       |a|
    {
        var m := p+(q-p)/2;
        if a[m] < x { p := m+1; }
        else        { q := m;   }
    }
    return p;

    /*
    // Recursive solution
    if a == [] { return 0; }
    var m := |a|/2;
    if a[m] >= x
    {
        k := BinarySearchFirstGE(a[..m],x);
    }
    else
    {
        k := BinarySearchFirstGE(a[m+1..],x);
        k := k+m+1;
    }
    */
}