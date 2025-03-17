include "BST.dfy"

method SearchLast100Recursive( t: BST ) returns( r: BST, ghost rp: seq<dir> )
    requires TreeIsSorted(t)
    ensures r==BSTEmpty ==> forall z|z in TreeSeq(t)::z>=100
    // The ghost output rp makes the postcondition simpler
    ensures r!=BSTEmpty ==>
        IsTreePath(t,rp) &&
        r == Subtree(t,rp) &&
        (forall z|z in PreSeqIncluding(t,rp)::z<100) &&
        (forall z|z in PostSeqExcluding(t,rp)::z>=100)
{
    RecursionSearchLemma(); // Not needed for human readers
    if t == BSTEmpty { return t,[]; }
    ExtendTreePath(t,[]);   // Not needed for human readers
    if RootValue(t)<100
    {
        r,rp := SearchLast100Recursive(Right(t));
        if r == BSTEmpty
        {
            r,rp := t,[];
        }
        else
        {
            ExtendTreePartitions(t,[1]+rp); // Not needed for human readers
            rp := [1]+rp;
        }
    }
    else
    {
        r,rp := SearchLast100Recursive(Left(t));
        if r != BSTEmpty { rp := [0]+rp; }
    }
}

method SearchLast100Loop( t: BST ) returns( r: BST )
    requires TreeIsSorted(t)
    ensures r==BSTEmpty ==> forall z|z in TreeSeq(t)::z>=100
    ensures r!=BSTEmpty ==>
        (exists rp|IsTreePath(t,rp)::
            r==Subtree(t,rp) &&
            (forall z|z in PreSeqIncluding(t,rp)::z<100) &&
            (forall z|z in PostSeqExcluding(t,rp)::z>=100)
        )
{
    var p: seq<dir> := [];
    r := BSTEmpty;
    var rp: seq<dir> := [];
    var s := t;
    while s != BSTEmpty
        decreases s
        invariant IsTreePath(t,p)
        invariant s == Subtree(t,p)
        invariant TreeIsSorted(s)
        invariant forall z|z in PreSeq(t,p)::z<100
        invariant forall z|z in PostSeq(t,p)::z>=100
        invariant r==BSTEmpty ==> PreSeq(t,p)==[]
        invariant r!=BSTEmpty ==>
            IsTreePath(t,rp) &&
            r == Subtree(t,rp) &&
            PreSeq(t,p)==PreSeqIncluding(t,rp)
    {
        // This next call is not necessary for human readers.
        // Þetta kall er óþarfi fyrir mannlega lesendur.
        ExtendTreePath(t,p);
        if RootValue(s) < 100
        {
            rp := p;
            r := s;
            s := Right(s);
            p := p+[1];
        }
        else
        {
            s := Left(s);
            p := p+[0];
        }
    }
    // The rest is not necessary for human readers.
    // Restin er óþarfi fyrir mannlega lesendur.
    TreePartitions(t,p);
    if r == BSTEmpty { return; }
    TreePartitions(t,rp);
    Concats(PreSeq(t,p),PostSeq(t,p),PostSeqExcluding(t,rp));
}

lemma Concats( a: seq<int>, b: seq<int>, c: seq<int> )
    decreases |b|+|c|
    requires a+b==a+c
    ensures b==c
{
    if b==[] || c==[] { return; }
    assert b[0]==(a+b)[|a|]==(a+c)[|a|]==c[0];
    assert b==b[..1]+b[1..];
    assert c==c[..1]+c[1..];
    assert a+b[..1]+b[1..]==a+b;
    Concats(a+b[..1],b[1..],c[1..]);
}