// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is

// Höfundur lausnar:     ...
// Permalink lausnar:    ...

// Insertion sort með hjálp helmingunarleitar.
// Insertion sort with the help of binary search.

method Search( s: seq<int>, x: int ) returns ( k: int )
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
    ensures 0 <= k <= |s|
    ensures forall i | 0 <= i < k :: s[i] <= x
    ensures forall i | k <= i < |s| :: s[i] >= x
    ensures forall z | z in s[..k] :: z <= x
    ensures forall z | z in s[k..] :: z >= x
    ensures s == s[..k]+s[k..]
{
    var p := 0;
    var q := |s|;
    while p != q
        decreases q-p
        invariant 0 <= p <= q <= |s|
        invariant forall i | 0 <= i < p :: s[i] < x
        invariant forall i | q <= i < |s| :: s[i] > x
    {
        var m := p+(q-p)/2;
        if s[m] == x { return m; }
        if s[m] < x  { p := m+1; }
        else         { q := m;   }
    }
    return p;
}

method Sort( m: multiset<int> ) returns ( r: seq<int> )
    ensures multiset(r) == m
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
{
    r := [];
    var rest := m;
    while rest != multiset{}
        decreases rest
        invariant m == multiset(r)+rest
        invariant forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
    {
        var x :| x in rest;
        rest := rest - multiset{x};
        var k := Search(r,x);
        r := r[..k]+[x]+r[k..];
    }
}