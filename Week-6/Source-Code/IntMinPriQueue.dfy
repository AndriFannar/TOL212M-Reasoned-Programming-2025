// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

trait IntMinPriQueue
{
    ghost var ghostbag: multiset<int>
    ghost var Repr: set<object>

    ghost predicate Valid()
        reads this, Repr

    predicate IsEmpty()
        reads this, Repr
        requires Valid()
        ensures IsEmpty() <==> |ghostbag| == 0

    ghost function Contents(): multiset<int>
        reads this
    {
        ghostbag
    }
    
    method Add( x: int )
        modifies this, Repr
        requires Valid()
        ensures Valid() && fresh(Repr-old(Repr))
        ensures ghostbag == old(ghostbag)+multiset{x}
    
    method RemoveMin() returns ( x: int )
        modifies this, Repr
        requires Valid()
        requires |ghostbag| != 0
        ensures Valid() && fresh(Repr-old(Repr))
        ensures x in old(ghostbag)
        ensures ghostbag == old(ghostbag)-multiset{x}
        ensures forall z | z in ghostbag :: x <= z
}