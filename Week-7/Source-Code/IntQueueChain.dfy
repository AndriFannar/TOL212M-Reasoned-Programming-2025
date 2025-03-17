// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

include "IntQueue.dfy"
include "Chain.dfy"

// Þessi biðraðarklasi notar eintengda lista breytanlegra hlekkja.
// This queue class uses a singly linked list of mutable links.
class IntQueueChain extends IntQueue
{
    var first: Link?<int>
    var last: Link?<int>
    var n: int
    ghost var linkseq: seq<Link<int>>

    // q.Valid() er satt þá og því aðeins að
    // eftirfarandi fastayrðing gagna sé sönn.
    // Biðröðin inniheldur tölurnar í keðju
    // hlekkja af tagi Link<int>. Ef biðröðin
    // er tóm þá er first==last==null. Ef ekki,
    // þá bendir first á fremsta hlekk keðjunnar
    // og last bendir á síðasta hlekk keðjunnar.
    // Fremsti hlekkurinn inniheldur fremsta gildi
    // biðraðarinnar og inniheldur bendi á næsta
    // hlekk (ef einhver er), sem inniheldur næsta
    // gildi, og svo koll af kolli. Aftasti
    // hlekkurinn inniheldur ekki bendi á annan
    // hlekk heldur null bendi í þess stað.
    // Auk þess þurfa draugabreyturnar Repr og
    // ghostseq að innihalda gildi sem samsvara
    // þessu ástandi, og einnig draugabreytan
    // linkseq sem inniheldur runu allra hlekkjanna
    // í keðjunni í röð sem samsvarar ghostseq.

    // q.Valid() is true if and only if the
    // following data invariant is true.
    // The queue contains the numbers in a chain
    // of links of type Link<int>. If the queue
    // is empty then first==last==null. If not,
    // then first refers to the first link of the
    // chain and lasr refers to the last link of
    // the chain.
    // The first link contains the frontmost value
    // of the queue and contains a reference to the
    // next link, if any, which contains the next
    // value, and so on and so forth. The last
    // link does not contain a reference to another
    // link but rather a null reference.
    // Also, the ghost variables Repr and ghostseq
    // must contain values that correspond to this
    // state, as well as the ghost variable linkseq
    // which contains the sequence of all the links
    // in the chain in an order that corresponds to
    // ghostseq.
    ghost predicate Valid()
        reads this, Repr
    {
        n == |ghostseq| &&
        (forall z | z in linkseq :: z in Repr) &&
        (forall z | z in Repr :: z in linkseq) &&
        (ghostseq == ValueSeq(linkseq)) &&
        (first == null ==>
            last == null &&
            linkseq == []
        ) &&
        (first != null ==>
            last != null &&
            linkseq != [] &&
            first in Repr &&
            last in Repr &&
            first.ValidChain(linkseq) &&
            last.ValidChain([last]) &&
            first == linkseq[0] &&
            last == linkseq[|linkseq|-1] &&
            last.tail == null &&
            forall i | 0 <= i < |linkseq|-1 ::
                linkseq[i].tail == linkseq[i+1]
        ) &&
        (forall p,q | 0 <= p < q < |linkseq| ::
            linkseq[p] != linkseq[q]
        )
    }

    constructor()
        ensures Valid()
        ensures Repr == {}         // <-- þrenging eftirskilyrðis
        ensures ghostseq == []     //     narrowing of postcondition
    {
        first := null;
        last := null;
        n := 0;
        Repr := {};
        ghostseq := [];
        linkseq := [];
    }

    predicate IsEmpty()
        reads this, Repr
        requires Valid()
        ensures IsEmpty() <==> ghostseq==[]
    {
        first == null
    }

    function Count(): int 
        reads this, Repr
        requires Valid()
        ensures Count() == |ghostseq|
    {
        n
    }
    
    method Put( x: int )
        modifies this, Repr
        requires Valid()
        ensures Valid() && fresh(Repr-old(Repr))
        ensures ghostseq == old(ghostseq)+[x]
        ensures Count() == old(Count())+1
    {
        first,linkseq,last := Append1(first,linkseq,last,x);
        Repr := Repr+{last};
        ghostseq := ghostseq+[x];
        n := n+1;
    }
    
    method Get() returns ( x: int )
        modifies this                          // <-- víkkun forskilyrðis
        requires Valid()                       //     widening of precondition
        requires ghostseq != []
        ensures Valid() && Repr < old(Repr)    // <-- þrenging eftirskilyrðis
        ensures ghostseq == old(ghostseq[1..]) //     narrowing of postcondition
        ensures x == old(ghostseq[0])
        ensures Count() == old(Count())-1
    {
        ValueSeqLemma(linkseq,ghostseq);
        x := first.head;
        assert x == ghostseq[0];
        assert multiset{x} == multiset(ghostseq[..1]);
        assert ghostseq == ghostseq[..1]+ghostseq[1..];
        Repr := Repr-{first};
        ghostseq := ghostseq[1..];
        linkseq := linkseq[1..];
        first := first.tail;
        if first == null { last := null; }
        n := n-1;
    }
}

method Factory() returns ( q: IntQueue )
    ensures fresh(q)
    ensures fresh(q.Repr)
    ensures q.Valid()
    ensures q.IsEmpty()
{
    q := new IntQueueChain();
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