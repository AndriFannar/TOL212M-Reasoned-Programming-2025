include "BST.dfy"

method Min( t: BST ) returns( m: int )
    requires TreeIsSorted(t)
    requires t != BSTEmpty
    ensures m in TreeSeq(t)
    ensures forall z | z in TreeSeq(t) :: z >= m
{
    if Left(t) == BSTEmpty
    {
        m := RootValue(t);
    }
    else
    {
        m := Min(Left(t));
    }
}