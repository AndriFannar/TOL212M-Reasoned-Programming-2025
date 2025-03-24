// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

trait IntMultiset
{
    ghost var ghostbag: multiset<int>
    ghost var Repr: set<object>
    
    ghost predicate Valid()
        reads this, Repr
    
    method Add( x: int )
        modifies this, Repr
        requires Valid()
        ensures Valid()
        ensures ghostbag == old(ghostbag)+multiset{x}
        ensures fresh(Repr-old(Repr))
    
    method Remove() returns( x: int )
        modifies this, Repr
        requires Valid()
        requires |ghostbag| != 0
        ensures Valid()
        ensures x in old(ghostbag)
        ensures ghostbag == old(ghostbag)-multiset{x}
        ensures fresh(Repr-old(Repr))
        
    predicate IsEmpty()
        reads this, Repr
        requires Valid()
        ensures IsEmpty() <==> |ghostbag| == 0
}