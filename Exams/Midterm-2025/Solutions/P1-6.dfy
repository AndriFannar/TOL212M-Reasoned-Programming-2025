include "BST.dfy"

// Loop solution
method SearchBetweenLoop( t: BST, a: int, b: int )
        returns( ghost rp: seq<dir>, r: BST )
    requires TreeIsSorted(t)
    requires a <= b
    ensures r == BSTEmpty ==>
                forall z | z in TreeSeq(t) :: !(a <= z <= b)
    ensures r != BSTEmpty ==>
                IsTreePath(t,rp) &&
                Subtree(t,rp) == r &&
                a <= RootValue(r) <= b
{
    var s := t;
    var sp := [];
    rp := [];
    while s != BSTEmpty
        decreases s
        invariant IsTreePath(t,sp)
        invariant s == Subtree(t,sp)
        invariant forall z | z in PreSeq(t,sp) :: z < a
        invariant forall z | z in PostSeq(t,sp) :: z > b
        invariant TreeIsSorted(s)
    {
        ExtendTreePath(t,sp);
        if RootValue(s) < a
        {
            s := Right(s);
            sp := sp+[1];
        }
        else if RootValue(s) > b
        {
            s := Left(s);
            sp := sp+[0];
        }
        else
        {
            r := s;
            rp := sp;
            TreePartitions(t,rp);
            return;
        }
    }
    TreePartitions(t,sp);
    r := BSTEmpty;
}

// Recursive solution
method SearchBetweenRecursive( t: BST, a: int, b: int )
        returns( ghost rp: seq<dir>, r: BST )
    decreases t
    requires TreeIsSorted(t)
    ensures r == BSTEmpty ==>
                forall z | z in TreeSeq(t) :: !(a <= z <= b)
    ensures r != BSTEmpty ==>
                IsTreePath(t,rp) &&
                Subtree(t,rp) == r &&
                a <= RootValue(r) <= b
{
    if t == BSTEmpty 
    {
        r := BSTEmpty;
        rp := [];
        return;
    }
    ExtendTreePath(t,[]);
    if RootValue(t) < a
    {
        rp, r := SearchBetweenRecursive(Right(t),a,b);
        rp := [1]+rp;
    }
    else if RootValue(t) > b
    {
        rp, r := SearchBetweenRecursive(Left(t),a,b);
        rp := [0]+rp;
    }
    else
    {
        r := t;
        rp := [];
        TreePartitions(t,rp);
    }
}