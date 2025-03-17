method Search( a: seq<int> ) returns( k: int )
    requires forall p,q | 0 <= p < q < |a| :: a[p] >= a[q];
    ensures -1 <= k < |a|;
    ensures forall i | 0 <= i <= k :: a[i] >= 100;
    ensures forall i | k < i < |a| :: a[i] < 100;

    // a: | >=100 | <100 |
    //     ^     ^        ^
    //     0     k       |a|

{
    /*
    // Loop solution:
    var p,q := 0,|a|;
    while p != q
        // | >=100 | ??? | <100 |
        //  ^       ^     ^      ^
        //  0       p     q     |a|
        decreases q-p;
        invariant 0 <= p <= q <= |a|;
        invariant forall i | 0 <= i < p :: a[i] >= 100;
        invariant forall i | q <= i < |a| :: a[i] < 100;
    {
        var m := p+(q-p)/2;
        if a[m] >= 100 { p := m+1; }
        else           { q := m;   }
    }
    k := p-1;
    */

    // Recursive solution:
    if |a| == 0 { return -1; }
    var m := |a|/2;
    if a[m] >= 100
    {
        k := Search(a[m+1..]);
        k := k+m+1;
    }
    else
    {
        k := Search(a[..m]);
    }
}
