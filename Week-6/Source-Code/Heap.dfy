// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

// You can see this on the web here: https://tinyurl.com/ypsfb5nr

include "Swapping.dfy"

predicate IsAncestorOf( p: int, q: int )
    decreases q
    requires 0 <= p
    requires 0 <= q
{
    p < q && (p == (q-1)/2 || IsAncestorOf(p,(q-1)/2))
}

lemma TransitiveAncestor( p: int, q: int, r: int )
    decreases r
    requires 0 <= p
    requires 0 <= q
    requires 0 <= r
    requires IsAncestorOf(p,q)
    requires IsAncestorOf(q,r)
    ensures  IsAncestorOf(p,r)
{
    if q == (r-1)/2 { return; }
}

lemma DescendantIsChildOrDescendantOfChild( p: int, q: int )
    requires 0 <= p
    requires 0 <= q
    requires IsAncestorOf(p,q)
    ensures q==2*p+1 || 
            q==2*p+2 || 
            IsAncestorOf(2*p+1,q) || 
            IsAncestorOf(2*p+2,q)
{
    // Depending on the version of Dafny you are using and
    // the speed and memory of your computer, you may or may
    // not need a body in this lemma.
    if p == (q-1)/2 { return; }
    DescendantIsChildOrDescendantOfChild(p,(q-1)/2);
    TransitiveAncestor(p,(q-1)/2,q);
}

lemma AllDescendantsAreChildrenOrDescendantsOfChild( p: int )
    requires 0 <= p
    ensures forall q | q >=0 && IsAncestorOf(p,q) ::
        q==2*p+1 || 
        q==2*p+2 || 
        IsAncestorOf(2*p+1,q) || 
        IsAncestorOf(2*p+2,q)
{
    forall q | q>=0 && IsAncestorOf(p,q)
    {
        DescendantIsChildOrDescendantOfChild(p,q);
    }
}

predicate IsMinHeap( a: seq<int>, i: int, j: int )
    requires 0 <= i <= j <= |a|
{
    forall p,q | i <= p < q < j && IsAncestorOf(p,q) :: a[p] <= a[q]
}

predicate IsMinHeapRollingDown( a: seq<int>, i: int, k: int, j: int )
    requires 0 <= i <= k < j <= |a|
{
    forall p,q | i <= p < q < j && IsAncestorOf(p,q) && p != k :: a[p] <= a[q]
}

lemma MinHeapRollingDownBecomesHeap( a: seq<int>, i: int, k: int, j: int )
    requires 0 <= i <= k < j <= |a|
    requires IsMinHeapRollingDown(a,i,k,j)
    ensures 2*k+1 >= j ==> IsMinHeap(a,i,j)
    ensures 2*k+1 < j && 2*k+2 >= j && a[k] <= a[2*k+1] ==> IsMinHeap(a,i,j)
    ensures 2*k+2 < j && a[k] <= a[2*k+1] && a[k] <= a[2*k+2] ==> IsMinHeap(a,i,j)
{
    if 2*k+1 >= j { return; }
    if 2*k+1 < j && 2*k+2 >= j && a[k] <= a[2*k+1] { return; }
    if 2*k+2 < j && a[k] <= a[2*k+1] && a[k] <= a[2*k+2]
    {
        if IsMinHeap(a,i,j) { return; }
        // Given that IsMinHeap(a,i,j) is false, we will derive a contradiction
        var p,q :| i <= p < q < j && IsAncestorOf(p,q) && a[p] > a[q];
        DescendantIsChildOrDescendantOfChild(p,q);
        assert false; // Yes! We have a contradiction, so IsMinHeap(a,i,j) is true
    }
}

method RollDownMinHeap( a: array<int>, i: int, j: int )
    modifies a
    requires 0 <= i < j <= a.Length
    requires IsMinHeap(a[..],i+1,j)
    ensures IsMinHeap(a[..],i,j)
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures a[..i] == old(a[..i])
    ensures a[j..] == old(a[j..])
    ensures multiset(a[i..j]) == old(multiset(a[i..j]))
{
    var k := i;
    var x := a[k];
    while true
        decreases j-k
        invariant i <= k < j
        invariant x == a[k]
        invariant IsMinHeapRollingDown(a[..],i,k,j)
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant a[..i] == old(a[..i])
        invariant a[j..] == old(a[j..])
        invariant multiset(a[i..j]) == old(multiset(a[i..j]))
    {
        var c := 2*k+1;
        if c >= j { return; }
        if c+1 < j && a[c+1] < a[c] { c := c+1; }
        MinHeapRollingDownBecomesHeap(a[..],i,k,j);
        if a[k] <= a[c] { return; }
        AllDescendantsAreChildrenOrDescendantsOfChild(k);
        ghost var olda := a[..];
        a[k], a[c] := a[c], a[k];
        SwappingLemma(olda,a[..],i,k,c,j);
        k := c;
    }
}

predicate IsMinHeapRollingUp( a: seq<int>, i: int, k: int, j: int )
    requires 0 <= i <= k < j <= |a|
{
    forall p,q | i <= p < q < j && IsAncestorOf(p,q) && q != k :: a[p] <= a[q]
}

method RollUpMinHeap( a: array<int>, j: int )
    modifies a
    requires 0 <= j < a.Length
    requires IsMinHeap(a[..],0,j)
    ensures IsMinHeap(a[..],0,j+1)
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures a[j+1..] == old(a[j+1..])
    ensures multiset(a[0..j+1]) == old(multiset(a[0..j+1]))
{
    var k := j;
    while true
        decreases k
        invariant 0 <= k <= j
        invariant IsMinHeapRollingUp(a[..],0,k,j+1)
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant a[j+1..] == old(a[j+1..])
        invariant multiset(a[0..j+1]) == old(multiset(a[0..j+1]))
    {
        if k == 0 { return; }
        var c := (k-1)/2;
        if a[k] >= a[c] { return; }
        AllDescendantsAreChildrenOrDescendantsOfChild(k);
        assert IsAncestorOf(c,k);
        ghost var olda := a[..];
        a[c], a[k] := a[k], a[c];
        SwappingLemma(olda,a[..],0,c,k,j+1);
        k := c;
    }
}

lemma PartOfHeap( a: seq<int>, i: int, j: int, p: int, q: int )
    requires 0 <= i <= p <= q <= j <= |a|
    requires IsMinHeap(a,i,j)
    ensures IsMinHeap(a,p,q)
{}

lemma ZeroIsRoot( p: int )
    decreases p
    requires p > 0
    ensures IsAncestorOf(0,p)
{
    if p == 1 || p == 2 { return; }
    ZeroIsRoot((p-1)/2);
    TransitiveAncestor(0,(p-1)/2,p);
}

lemma RootHasMin( a: seq<int>, i: int, j: int )
    requires 0 <= i <= j <= |a|
    requires IsMinHeap(a,i,j)
    ensures forall p | i <= p < j && IsAncestorOf(i,p) :: a[i] <= a[p]
{}

lemma ZeroHasMin( a: seq<int>, n: int )
    requires 0 < n <= |a|
    requires IsMinHeap(a,0,n)
    ensures forall p | 0 < p < n :: IsAncestorOf(0,p)
    ensures forall p | 0 <= p < n :: a[0] <= a[p]
{
    forall p | 1 <= p < n { ZeroIsRoot(p); }
}