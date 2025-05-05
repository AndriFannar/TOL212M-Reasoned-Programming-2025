include "BST.dfy"

method HasNegative( t: BST ) returns( r: bool )
    requires TreeIsSorted(t)
    ensures r ==> exists z | z in TreeSeq(t) :: z < 0
    ensures !r ==> forall z | z in TreeSeq(t) :: z >= 0
{
    if t == BSTEmpty { return false; }
    if RootValue(t) < 0
    {
        assert RootValue(t) in TreeSeq(t);
        return true;
    }
    r := HasNegative(Left(t));
    assert forall z | z in TreeSeq(Left(t)) :: z in TreeSeq(t);
}