include "BST.dfy"

method LastLT100Recursive( t: BST ) returns( r: BST, ghost rp: seq<dir> )
    requires TreeIsSorted(t)
    ensures r == BSTEmpty ==>
                forall z | z in TreeSeq(t) :: z >= 100
    ensures r != BSTEmpty ==>
                IsTreePath(t,rp) &&
                r == Subtree(t,rp) &&
                (forall z | z in PreSeqIncluding(t,rp) :: z < 100) &&
                (forall z | z in PostSeqExcluding(t,rp) :: z >= 100)
{
    RecursionSearchLemma();
    if t == BSTEmpty
    {
        r := BSTEmpty;
        rp := [];
        return;
    }
    if RootValue(t) >= 100
    {
        r,rp := LastLT100Recursive(Left(t));
        if r == BSTEmpty { return; }
        rp := [0]+rp;
        return;
    }
    r,rp := LastLT100Recursive(Right(t));
    if r != BSTEmpty
    {
        rp := [1]+rp;
        return;
    }
    rp := [];
    r := t;
}

method LastLT100Loop( t: BST ) returns( r: BST, ghost rp: seq<dir> )
    requires TreeIsSorted(t)
    ensures r == BSTEmpty ==>
                forall z | z in TreeSeq(t) :: z >= 100
    ensures r != BSTEmpty ==>
                IsTreePath(t,rp) &&
                r == Subtree(t,rp) &&
                (forall z | z in PreSeqIncluding(t,rp) :: z < 100) &&
                (forall z | z in PostSeqExcluding(t,rp) :: z >= 100)
{
    rp := [];
    var s := t;
    var sp: seq<dir> := [];
    r := BSTEmpty;
    while s != BSTEmpty
        decreases s
        invariant IsTreePath(t,sp)
        invariant s == Subtree(t,sp)
        invariant forall z | z in PreSeq(t,sp) :: z < 100
        invariant forall z | z in PostSeq(t,sp) :: z >= 100
        invariant r == BSTEmpty ==>
            PreSeq(t,sp) == []
        invariant r != BSTEmpty ==>
            PreSeq(t,sp) != [] &&
            IsTreePath(t,rp) &&
            r == Subtree(t,rp) &&
            PreSeqIncluding(t,rp) == PreSeq(t,sp) &&
            PostSeqExcluding(t,rp) == TreeSeq(s)+PostSeq(t,sp)
        invariant TreeIsSorted(s)
    {
        ExtendTreePath(t,sp);
        if RootValue(s) < 100
        {
            rp := sp;
            r := s;
            sp := sp+[1];
            s := Right(s);
        }
        else
        {
            sp := sp+[0];
            s := Left(s);
        }
    }
    TreePartitions(t,sp);
    if r == BSTEmpty { return; }
    TreePartitions(t,rp);
}