include "BST.dfy"

method LeftmostPositive( t: BST ) returns( r: BST, ghost p: seq<dir> )
    requires TreeIsSorted(t)
    ensures r == BSTEmpty ==> forall z | z in TreeSeq(t) :: z <= 0
    ensures r != BSTEmpty ==>
        IsTreePath(t,p) &&
        r == Subtree(t,p) &&
        (forall z | z in PreSeqExcluding(t,p) :: z <= 0) &&
        (forall z | z in PostSeqIncluding(t,p) :: z > 0)
{
    RecursionSearchLemma();
    if t == BSTEmpty { return t,[]; }
    if RootValue(t) <= 0
    {
        r, p := LeftmostPositive(Right(t));
        if r != BSTEmpty { p := [1]+p; }
        return;
    }
    r, p := LeftmostPositive(Left(t));
    if r != BSTEmpty
    {
        p := [0]+p;
        return;
    }
    r, p := t, [];
}

method LeftmostPositiveLoop( t: BST ) returns( r: BST, ghost p: seq<dir> )
    requires TreeIsSorted(t)
    ensures r == BSTEmpty ==> forall z | z in TreeSeq(t) :: z <= 0
    ensures r != BSTEmpty ==>
        IsTreePath(t,p) &&
        r == Subtree(t,p) &&
        (forall z | z in PreSeqExcluding(t,p) :: z <= 0) &&
        (forall z | z in PostSeqIncluding(t,p) :: z > 0)
{
    r := BSTEmpty;
    p := [];
    var s := t;
    ghost var sp := [];
    while s != BSTEmpty
        decreases s
        invariant IsTreePath(t,sp)
        invariant s == Subtree(t,sp)
        invariant forall z | z in PreSeq(t,sp) :: z <= 0
        invariant forall z | z in PostSeq(t,sp) :: z > 0
        invariant r == BSTEmpty ==> forall z | z in PreSeq(t,sp) :: z <= 0
        invariant r == BSTEmpty ==> PostSeq(t,sp) == []
        invariant r != BSTEmpty ==> 
            IsTreePath(t,p) &&
            r == Subtree(t,p) &&
            PreSeqExcluding(t,p) == PreSeq(t,sp)+TreeSeq(s) &&
            PostSeq(t,sp) == PostSeqIncluding(t,p)
        invariant TreeIsSorted(s)
    {
        ExtendTreePath(t,sp);
        if RootValue(s) > 0
        {
            r := s;
            p := sp;
            s := Left(s);
            sp := sp+[0];
        }
        else
        {
            s := Right(s);
            sp := sp+[1];
        }
    }
    TreePartitions(t,sp);
    if r == BSTEmpty { return; }
    TreePartitions(t,p);
}