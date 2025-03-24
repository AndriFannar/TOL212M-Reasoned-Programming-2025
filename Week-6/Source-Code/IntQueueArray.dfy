// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

include "IntQueue.dfy"

class IntQueueArray extends IntQueue
{
    var a: array<int>
    var front: int
    var size: int

    ghost predicate Valid()
        reads this, Repr
    {
        Repr == {this,a} &&
        a.Length > 0 &&
        0 <= size <= a.Length &&
        0 <= front < a.Length &&
        |ghostseq| == size &&
        if front+size <= a.Length then
            ghostseq == a[front..front+size]
        else
            ghostseq == a[front..]+a[..front+size-a.Length]
    }

    constructor()
        ensures Valid() && fresh(Repr-{this})
        ensures ghostseq == []
    {
        a := new int[1];
        front := 0;
        size := 0;
        Repr := {this,a};
        ghostseq := [];
    }

    predicate IsEmpty()
        reads this, Repr
        requires Valid()
        ensures IsEmpty() <==> ghostseq==[]
    {
        size == 0
    }

    function Count(): int 
        reads this, Repr
        requires Valid()
        ensures Count() == |ghostseq|
	{
		size
	}
	
    method Put( x: int )
        modifies this, Repr
        requires Valid()
        ensures Valid() && fresh(Repr-old(Repr))
        ensures ghostseq == old(ghostseq)+[x]
        ensures Count() == old(Count())+1
    {
        if size == a.Length
        {
            var newa := new int[2*a.Length];
            var i := 0;
            var j := front;
            while i < size && j != a.Length
                decreases size-i
                invariant 0 <= j <= a.Length
                invariant 0 <= i <= |ghostseq| == size <= a.Length < newa.Length
                invariant j == front+i
                invariant newa[..i] == ghostseq[..i]
                invariant ghostseq == old(ghostseq)
                invariant Valid()
            {
                newa[i] := a[j];
                i := i+1;
                assert newa[..i] == ghostseq[..i];
                j := j+1;
            }
            if j == a.Length
            {
                j := 0;
                assert j == front+i-a.Length;
                while i < size
                    decreases size-i
                    invariant 0 <= j <= size <= a.Length
                    invariant 0 <= i <= |ghostseq| == size <= a.Length < newa.Length
                    invariant j == front+i-a.Length
                    invariant newa[..i] == ghostseq[..i]
                    invariant ghostseq == old(ghostseq)
                    invariant Valid()
                {
                    newa[i] := a[j];
                    i := i+1;
                    j := j+1;
                }
            }
            a := newa;
            Repr := {this,a};
            front := 0;
        }
        if front+size >= a.Length
        {
            a[front+size-a.Length] := x;
        }
        else
        {
            a[front+size] := x;
        }
        size := size+1;
        ghostseq := ghostseq+[x];
    }
    
    method Get() returns ( x: int )
        modifies this, Repr
        requires Valid()
        requires ghostseq != []
        ensures Valid() && fresh(Repr-old(Repr))
        ensures ghostseq == old(ghostseq[1..])
        ensures x == old(ghostseq[0])
        ensures Count() == old(Count())-1
    {
        size := size-1;
        x := a[front];
        front := front+1;
        ghostseq := ghostseq[1..];
        if front == a.Length { front := 0; }
    }
}

method Factory() returns ( q: IntQueue )
    ensures fresh(q)
    ensures fresh(q.Repr)
    ensures q.Valid()
    ensures q.IsEmpty()
{
    q := new IntQueueArray();
}

method Main()
{
    var q1 := Factory();
    var q2 := Factory();
    var q3 := Factory();
    var q4 := Factory();
    q1.Put(1);
    q2.Put(1);
    q3.Put(1);
    q4.Put(1);
    q1.Put(2);
    assert q1.ghostseq == [1,2];
    assert q2.ghostseq == [1];
    assert q3.ghostseq == [1];
    assert q4.ghostseq == [1];
    q2.Put(3);
    q3.Put(4);
    q4.Put(5);
    assert q1.ghostseq == [1,2];
    assert q2.ghostseq == [1,3];
    assert q3.ghostseq == [1,4];
    assert q4.ghostseq == [1,5];
    var x;
    x := q1.Get(); print x; print " ";
    assert x == 1;
    x := q1.Get(); print x; print " ";
    assert x == 2;
    assert q1.ghostseq == [];
    x := q2.Get(); print x; print " ";
    x := q2.Get(); print x; print " ";
    x := q3.Get(); print x; print " ";
    x := q3.Get(); print x; print " ";
    x := q4.Get(); print x; print " ";
    x := q4.Get(); print x; print " ";
    assert q1.IsEmpty();
    assert q2.IsEmpty();
    assert q3.IsEmpty();
    assert q4.IsEmpty();
}