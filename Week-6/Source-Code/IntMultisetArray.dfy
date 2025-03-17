// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

include "IntMultiset.dfy"

class IntMultisetArray extends IntMultiset
{
    var a: array<int>
    var size: int

    ghost predicate Valid()
        reads this, Repr
    {
        Repr == {this,a} &&
        0 <= size <= a.Length &&
        multiset(a[..size]) == ghostbag &&
        a.Length > 0
    }

    constructor()
        ensures Valid() && fresh(Repr-{this})
        ensures |ghostbag| == 0
    {
        a := new int[100];
        size := 0;
        Repr := {this,a};
        ghostbag := multiset{};
    }

    predicate IsEmpty()
        reads this, Repr
        requires Valid()
        ensures IsEmpty() <==> |ghostbag| == 0
    {
        size == 0
    }
    
    method Add( x: int )
        modifies this, Repr
        requires Valid()
        ensures Valid()
        ensures fresh(Repr-old(Repr))
        ensures ghostbag == old(ghostbag)+multiset{x}
    {
        if size == a.Length
        {
            var newa := new int[2*a.Length];
            assert newa.Length > a.Length;
            var i := 0;
            while i != size
                decreases size-i
                invariant 0 <= i <= size <= a.Length < newa.Length
                invariant newa[..i] == a[..i]
                invariant ghostbag == old(ghostbag)
                invariant Valid()
            {
                newa[i] := a[i];
                i := i+1;
            }
            a := newa;
            Repr := {this,a};
        }
        a[size] := x;
        size := size+1;
        ghostbag := ghostbag+multiset{x};
    }
    
    method Remove() returns ( x: int )
        modifies this, Repr
        requires Valid()
        requires |ghostbag| != 0
        ensures Valid()
        ensures fresh(Repr-old(Repr))
        ensures x in old(ghostbag)
        ensures ghostbag == old(ghostbag)-multiset{x}
    {
        size := size-1;
        x := a[size];
        ghostbag := ghostbag-multiset{x};
    }
}

method Factory() returns( m: IntMultiset )
    ensures fresh(m)
    ensures fresh(m.Repr)
    ensures m.Valid()
    ensures m.IsEmpty()
{
    m := new IntMultisetArray();
}

method Test( s: seq<int> )
{
    var m := Factory();
    var i := 0;
    while i != |s|
        decreases |s|-i
        invariant 0 <= i <= |s|
        invariant m.Valid()
        invariant m.ghostbag == multiset(s[..i])
        invariant fresh(m.Repr)
    {
        m.Add(s[i]);
        assert s[..i]+[s[i]] == s[..i+1];
        i := i+1;
    }
    assert s == s[..i];
    ghost var removed: multiset<int> := multiset{};
    while !m.IsEmpty()
        invariant m.Valid()
        decreases m.ghostbag
        invariant m.ghostbag+removed == multiset(s)
        invariant fresh(m.Repr)
    {
        var x := m.Remove();
        removed := removed+multiset{x};
    }
    assert removed == multiset(s);
    assert |m.ghostbag| == 0;
}