include "BST.dfy"

// Compile using:
//   dafny build BSTSort.dfy BST.doo --verification-time-limit:1000
// OR, if the above include is uncommented, using:
//   dafny build BSTSort.dfy --verification-time-limit:1000

method Sort( a: array<int> )
    modifies a
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall i,j | 0 <= i < j < a.Length :: a[i] <= a[j]
{
    var t := BSTEmpty;
    var i := 0;

    assert TreeSeq(t) == [];

    while i != a.Length
        invariant 0 <= i <= a.Length
        invariant TreeIsSorted(t)
        invariant multiset(TreeSeq(t)) == multiset(a[..i])
        invariant a[..] == old(a[..])
    {
        t := Insert(t,a[i]);
        i := i+1;
    }

    assert i == a.Length;
    assert a[..] == a[..i];
    assert multiset(a[..]) == multiset(TreeSeq(t));
    assert a[..] == old(a[..]);
    assert a[i..] == [];

    while i != 0
        invariant 0 <= i <= a.Length
        invariant TreeIsSorted(t)
        invariant old(multiset(a[..])) == multiset(TreeSeq(t))+multiset(a[i..])
        invariant forall u,v | u in TreeSeq(t) && v in a[i..] :: u <= v 
        invariant forall p,q | i <= p < q < a.Length :: a[p] <= a[q]
    {
        ghost var oldt := t;
        ghost var olda := a[..];

        i := i-1;
        t, a[i] := DeleteMax(t);

        assert a[i] in TreeSeq(oldt);
        assert a[i+1..] == olda[i+1..];
        assert forall r | i < r < a.Length :: a[r] in olda[i+1..];
        assert forall r | i < r < a.Length :: a[r] == olda[r];
        assert forall r | i < r < a.Length :: a[i] <= olda[r];
        assert forall r | i < r < a.Length :: a[i] <= a[r];
        assert multiset(TreeSeq(t)) == multiset(TreeSeq(oldt))-multiset{a[i]};
        assert a[i..] == a[i..i+1]+olda[i+1..];
        calc == 
        {
            old(multiset(a[..]));
            multiset(TreeSeq(oldt))+multiset(olda[i+1..]);
            multiset(TreeSeq(t))+multiset{a[i]}+multiset(a[i+1..]);
        }
    }
}