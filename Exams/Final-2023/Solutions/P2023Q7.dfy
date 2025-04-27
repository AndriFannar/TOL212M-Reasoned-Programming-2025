/*
Write a function that searches in a binary search tree and returns a reference
to the rightmost node that contains a negative number (a number less than zero), 
or returns BSTEmpty is such a node does not exist in the tree.
*/

include "BST.dfy"

method FindLastNegative( t: BST ) returns( r: BST, ghost p: seq<dir> )
    decreases t
    requires TreeIsSorted(t)
    ensures r == BSTEmpty ==> forall z | z in TreeSeq(t) :: z >= 0
    ensures r != BSTEmpty ==>
        IsTreePath(t,p) &&
        r == Subtree(t,p) &&
        (forall z | z in PreSeqIncluding(t,p) :: z < 0) &&
        (forall z | z in PostSeqExcluding(t,p) :: z >= 0)
{
    RecursionSearchLemma(); // Not needed for human grading, but Dafny needs it
    if t == BSTEmpty
    {
        r, p := t, [];
    }
    else if RootValue(t) < 0
    {
        r, p := FindLastNegative(Right(t));
        if r == BSTEmpty { r, p := t, []; }
        else             { p := [1]+p;    }
   }
    else
    {
        r, p := FindLastNegative(Left(t));
        p := [0]+p;
    }
}