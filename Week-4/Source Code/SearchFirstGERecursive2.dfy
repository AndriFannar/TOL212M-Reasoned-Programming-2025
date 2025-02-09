include "BST.dfy"

method SearchFirstGERecursive2( t: BST, x: int ) returns( r: BST, ghost rp: seq<dir> )
    decreases t
    requires TreeIsSorted(t)
    ensures r == BSTEmpty ==>
        (forall z | z in TreeSeq(t) :: z < x)
    ensures r != BSTEmpty ==>
        IsTreePath(t,rp) &&
        r == Subtree(t,rp) &&
        (forall z | z in PreSeqExcluding(t,rp) :: z < x) &&
        (forall z | z in PostSeqIncluding(t,rp) :: z >= x)
{
    RecursionSearchLemma();
    if t == BSTEmpty { return BSTEmpty, []; }
    if RootValue(t) < x
    {
        r, rp := SearchFirstGERecursive2(Right(t),x);
        rp := [1]+rp;
    }
    else
    {
        r, rp := SearchFirstGERecursive2(Left(t),x);
        if r == BSTEmpty { return t, []; }
        rp := [0]+rp;
    }
}

method SearchFirstGERecursive3( t: BST, x: int ) returns( r: BST )
    decreases t
    requires TreeIsSorted(t)
    ensures r == BSTEmpty ==>
        (forall z | z in TreeSeq(t) :: z < x)
    ensures r != BSTEmpty ==>
        exists rp | IsTreePath(t,rp) ::
            r == Subtree(t,rp) &&
            (forall z | z in PreSeqExcluding(t,rp) :: z < x) &&
            (forall z | z in PostSeqIncluding(t,rp) :: z >= x)
{
    RecursionSearchLemma();
    if t == BSTEmpty { return BSTEmpty; }
    if RootValue(t) < x
    {
        r := SearchFirstGERecursive3(Right(t),x);
        if r == BSTEmpty { return; }

        // The following ghostly lines are needed to convince Dafny that
        // the postconditions are satisfied when r != BSTEmpty
        ghost var rp :| IsTreePath(Right(t),rp) &&
            r == Subtree(Right(t),rp) &&
            (forall z | z in PreSeqExcluding(Right(t),rp) :: z < x) &&
            (forall z | z in PostSeqIncluding(Right(t),rp) :: z >= x);
        rp := [1]+rp;
        assert IsTreePath(t,rp) &&
            r == Subtree(t,rp) &&
            (forall z | z in PreSeqExcluding(t,rp) :: z < x) &&
            (forall z | z in PostSeqIncluding(t,rp) :: z >= x);
    }
    else
    {
        // This assert is needed to convince Dafny that
        // the postconditions are satisfied when r == BSTEmpty
        assert forall z | z in PostSeqIncluding(t,[]) :: z >= x;

        r := SearchFirstGERecursive3(Left(t),x);
        if r == BSTEmpty { return t; }

        // The following ghostly lines are needed to convince Dafny that
        // the postconditions are satisfied when r != BSTEmpty
        ghost var rp :| IsTreePath(Left(t),rp) &&
            r == Subtree(Left(t),rp) &&
            (forall z | z in PreSeqExcluding(Left(t),rp) :: z < x) &&
            (forall z | z in PostSeqIncluding(Left(t),rp) :: z >= x);
        rp := [0]+rp;
        assert IsTreePath(t,rp) &&
            r == Subtree(t,rp) &&
            (forall z | z in PreSeqExcluding(t,rp) :: z < x) &&
            (forall z | z in PostSeqIncluding(t,rp) :: z >= x);
    }
}
