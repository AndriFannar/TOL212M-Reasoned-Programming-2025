// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is

// Höfundur lausnar:     ...
// Permalink lausnar:    ...

// Klárið að forrita klasann IntQueueCycle
// með því að forrita stofnana á aðferðunum
// IsEmpty, Put og Get, ásamt smiðnum fyrir
// klasann.
// Allt sem til þarf er í þessari skrá og þið
// ættuð ekki að þurfa að kalla á neinar
// hjálparsetningar eða setja nein assert.
// Athugið að ósennilegt er að unnt sé að
// vinna þetta verkefni á rise4fun vefsíðunni.

include "Cycle.dfy"

class IntQueueCycle<T> extends Queue<T>
{
    var last: Link?<T>
    ghost var cycle: seq<Link<T>>

    ghost predicate Valid()
        reads this, Repr
    {
        (last != null ==> last in Repr) &&
        (forall z | z in cycle :: z in Repr) &&
        (forall z | z in Repr :: z in cycle) &&
        (ghostseq == ValueSeq(cycle)) &&
        (last == null ==> cycle == []) &&
        (last != null ==> last.ValidCycle(cycle)) &&
        (|cycle| == |ghostseq|) &&
        (forall i | 0 <= i < |cycle| :: cycle[i].head == ghostseq[i])
    }

    constructor()
        ensures Valid()
        ensures Repr == {}
        ensures ghostseq == []
    {
        // Gefum tilviksbreytunum last, Repr, ghostseq og cycle
        // rétt gildi miðað við fastayrðingu gagna og eftirskilyrði.
        last := null;
        Repr := {};
        ghostseq := [];
        cycle := [];
        new;
        assert  // Þetta assert er sama og fastayrðing gagna
                // og er óþarfi ef smiðurinn er rétt forritaður,
                // en ef ekki þá hjálpar þetta að finna villur.
            (last != null ==> last in Repr) &&
            (forall z | z in cycle :: z in Repr) &&
            (forall z | z in Repr :: z in cycle) &&
            (ghostseq == ValueSeq(cycle)) &&
            (last == null ==> cycle == []) &&
            (last != null ==> last.ValidCycle(cycle)) &&
            |cycle| == |ghostseq| &&
            (forall i | 0 <= i < |cycle| :: cycle[i].head == ghostseq[i]);
        
    }

    predicate IsEmpty()
        reads this, Repr
        requires Valid()
        ensures IsEmpty() <==> ghostseq==[]
    {
        last == null
    }
    
    method Put( x: T )
        modifies this, Repr
        requires Valid()
        ensures Valid()
        ensures fresh(Repr-old(Repr))
        ensures ghostseq == old(ghostseq)+[x]
    {
        last := new Link(x,last,cycle,ghostseq);
        ghostseq := ghostseq+[x];
        cycle := cycle+[last];
        Repr := Repr+{last};
    }
    
    method Get() returns ( x: T )
        modifies this, Repr
        requires Valid()
        requires ghostseq != []
        ensures Valid()
        ensures Repr < old(Repr)
        ensures ghostseq == old(ghostseq[1..])
        ensures x == old(ghostseq[0])
    {
        x := last.tail.head;
        Repr := Repr-{last.tail};
        last,cycle,ghostseq := RemoveFirst(last,cycle,ghostseq);
    }
}

///////////////////////////////////////////////////////////////
// Hér lýkur breytanlega hluta skrárinnar.
// Ekki breyta því sem er hér fyrir neðan.
///////////////////////////////////////////////////////////////

// Hér er grunnskilgreiningin á hegðun biðraðar.
trait Queue<T>
{
    ghost var ghostseq: seq<T>
    ghost var Repr: set<object>

    ghost predicate Valid()
        reads this, Repr

    predicate IsEmpty()
        reads this, Repr
        requires Valid()
        ensures IsEmpty() <==> ghostseq==[]
    
    method Put( x: T )
        modifies this, Repr
        requires Valid()
        ensures Valid() && fresh(Repr-old(Repr))
        ensures ghostseq == old(ghostseq)+[x]
    
    method Get() returns ( x: T )
        modifies this, Repr
        requires Valid()
        requires ghostseq != []
        ensures Valid() && fresh(Repr-old(Repr))
        ensures ghostseq == old(ghostseq[1..])
        ensures x == old(ghostseq[0])
}

method Factory() returns ( q: Queue<int> )
    ensures fresh(q)
    ensures fresh(q.Repr)
    ensures q.Valid()
    ensures q.IsEmpty()
{
    q := new IntQueueCycle<int>();
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
    q2.Put(2);
    q3.Put(2);
    q4.Put(2);
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