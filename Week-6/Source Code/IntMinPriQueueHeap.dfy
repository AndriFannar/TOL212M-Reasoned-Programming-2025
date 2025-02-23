// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

include "IntMinPriQueue.dfy"
include "Heap.dfy"

// Compile with
//  dafny build --verify-included-files IntMinPriQueueHeap.dfy
// For some reason the current Dafny does not compile enough methods
// in Heap.dfy unless we specify the option --verify-included-files.

class IntMinPriQueueHeap extends IntMinPriQueue
{
    var a: array<int>
    var n: int

    ghost predicate Valid()
        reads this, Repr
    {
        Repr == {a,this} &&
        a.Length >= 2 &&
        0 <= n <= a.Length &&
        IsMinHeap(a[..],0,n) &&
        multiset(a[..n]) == ghostbag
    }
    
    constructor()
        ensures Valid() && fresh(Repr-{this})
        ensures ghostbag == multiset{}
    {
        n := 0;
        ghostbag := multiset{};
        a := new int[2];
        Repr := {a,this};
    }

    predicate IsEmpty()
        reads this, Repr
        requires Valid()
        ensures IsEmpty() <==> |ghostbag| == 0
    {
        n == 0
    }
    
    method Add( x: int )
        modifies this, Repr
        requires Valid()
        ensures Valid() && fresh(Repr-old(Repr))
        ensures ghostbag == old(ghostbag)+multiset{x}
    {
        if n == a.Length
        {
            var newa := new int[2*a.Length];
            var i := 0;
            while i < n
                decreases n-i
                invariant 0 <= i <= |ghostbag| == n <= a.Length < newa.Length
                invariant a == old(a)
                invariant a[..] == old(a[..])
                invariant newa[..i] == a[..i]
                invariant ghostbag == old(ghostbag)
                invariant Valid()
            {
                newa[i] := a[i];
                i := i+1;
            }
            a := newa;
            Repr := {a,this};
        }
        a[n] := x;
        RollUpMinHeap(a,n);
        ghostbag := ghostbag+multiset{x};
        n := n+1;
    }

    method RemoveMin() returns ( x: int )
        modifies this, Repr
        requires Valid()
        requires |ghostbag| != 0
        ensures Valid() && fresh(Repr-old(Repr))
        ensures x in old(ghostbag)
        ensures ghostbag == old(ghostbag)-multiset{x}
        ensures forall z | z in ghostbag :: x <= z
    {
        ZeroHasMin(a[..],n);
        x := a[0];
        n := n-1;
        ghostbag := ghostbag-multiset{x};
        if n == 0 { return; }
        a[0] := a[n];
        RollDownMinHeap(a,0,n);
    }
}

method Factory() returns( pq: IntMinPriQueueHeap )
    ensures fresh(pq)
    ensures fresh(pq.Repr)
    ensures pq.Valid()
    ensures pq.IsEmpty()
{
    pq := new IntMinPriQueueHeap();
}

method Sort( s: seq<int> ) returns( r: seq<int> )
    ensures multiset(s) == multiset(r)
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
{
    var p: IntMinPriQueue := Factory();
    var p2: IntMinPriQueue := Factory();
    var i := 0;
    while i != |s|
        invariant 0 <= i <= |s|
        decreases |s|-i

        invariant p.Valid()
        invariant p.Contents() == multiset(s[..i])
        invariant fresh(p.Repr)

        invariant p2.Valid()
        invariant p2.Contents() == multiset(s[..i])
        invariant fresh(p2.Repr)

        invariant p.Repr !! p2.Repr
    {
        p.Add(s[i]);
        p2.Add(s[i]);
        i := i+1;
        assert s[..i] == s[..i-1]+s[i-1..i];
    }
    r := [];
    assert s == s[..i];
    while !p.IsEmpty()
        decreases p.Contents()
        invariant p.Valid()
        invariant fresh(p.Repr)
        invariant multiset(s) == p.Contents()+multiset(r)
        invariant forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
        invariant forall x,q | x in p.Contents() && 0 <= q < |r| :: r[q] <= x
    {
        var x := p.RemoveMin();
        r := r+[x];
    }
}

method Main()
{
    var r := Sort([9,1,8,2,7,3,6,4,5,9,1,8,2,7,3,6,4,5]);
    print r;
}