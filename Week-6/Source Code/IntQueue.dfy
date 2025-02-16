// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

trait IntQueue
{
    ghost var ghostseq: seq<int>
    ghost var Repr: set<object>

    ghost predicate Valid()
        reads this, Repr

    predicate IsEmpty()
        reads this, Repr
        requires Valid()
        ensures IsEmpty() <==> ghostseq==[]
    
    method Put( x: int )
        modifies this, Repr
        requires Valid()
        ensures Valid() && fresh(Repr-old(Repr))
        ensures ghostseq == old(ghostseq)+[x]
        ensures Count() == old(Count())+1
    
    method Get() returns ( x: int )
        modifies this, Repr
        requires Valid()
        requires ghostseq != []
        ensures Valid() && fresh(Repr-old(Repr))
        ensures ghostseq == old(ghostseq[1..])
        ensures x == old(ghostseq[0])
        ensures Count() == old(Count())-1
    
    function Count(): int 
        reads this, Repr
        requires Valid()
        ensures Count() == |ghostseq|

    ghost function Contents(): seq<int>
        reads this, Repr
        requires Valid()
    {
        ghostseq
    }
}