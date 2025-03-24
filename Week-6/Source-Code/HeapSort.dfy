// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

include "Heap.dfy"

method Sort( a: array<int> )
    modifies a
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall p,q | 0 <= p < q < a.Length :: a[p] >= a[q]
{
    if a.Length == 0 { return; }
    var i := a.Length/2;
    while i != 0
        decreases i
        invariant 0 <= i <= a.Length
        invariant IsMinHeap(a[..],i,a.Length)
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        i := i-1;
        RollDownMinHeap(a,i,a.Length);
    }
    i := a.Length;
    while i != 1
        decreases i
        invariant 1 <= i <= a.Length
        invariant IsMinHeap(a[..],0,i)
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant forall p,q | 0 <= p < i <= q < a.Length :: a[p] >= a[q]
        invariant forall p,q | i <= p < q < a.Length :: a[p] >= a[q]
    {
        PartOfHeap(a[..],0,i,1,i-1);
        ZeroHasMin(a[..],i);
        i := i-1;
        a[0], a[i] := a[i], a[0];
        ghost var preset := multiset(a[..i]);
        RollDownMinHeap(a,0,i);
        assert forall p | 0 <= p < i :: a[p] in preset;
    }
}

method Sort2( a: array<int> )
    modifies a
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall p,q | 0 <= p < q < a.Length :: a[p] >= a[q]
{
    if a.Length == 0 { return; }
    var i := 0;
    while i != a.Length
        decreases a.Length-i
        invariant 0 <= i <= a.Length
        invariant IsMinHeap(a[..],0,i)
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        RollUpMinHeap(a,i);
        i := i+1;
    }
    i := a.Length;
    while i != 1
        decreases i
        invariant 1 <= i <= a.Length
        invariant IsMinHeap(a[..],0,i)
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant forall p,q | 0 <= p < i <= q < a.Length :: a[p] >= a[q]
        invariant forall p,q | i <= p < q < a.Length :: a[p] >= a[q]
    {
        PartOfHeap(a[..],0,i,1,i-1);
        ZeroHasMin(a[..],i);
        i := i-1;
        a[0], a[i] := a[i], a[0];
        ghost var preset := multiset(a[..i]);
        RollDownMinHeap(a,0,i);
        assert forall p | 0 <= p < i :: a[p] in preset;
    }
}

method Main()
{
    var a' := [9,1,8,2,7,3,6,4,5,100];
    var a := new int[|a'|](i=>if 0<=i<|a'| then a'[i] else 0);
    Sort2(a);
    var i := 0;
    while i != a.Length
        decreases a.Length-i
        invariant 0 <= i <= a.Length
    {
        print a[i];
        print " ";
        i := i+1;
    }
}