include "BST.dfy"

method SearchLastLTSimpleRecursive( t: BST, x: int ) returns ( r: BST, ghost rp: seq<dir> )
    decreases t
	requires TreeIsSorted(t)
    ensures IsTreePath(t,rp)
    ensures r == BSTEmpty ==>
        (forall z | z in TreeSeq(t) :: z >= x)
	ensures r != BSTEmpty ==>
        IsTreePath(t,rp) &&
        r == Subtree(t,rp) &&
        (forall z | z in PreSeqIncluding(t,rp) :: z < x) &&
        (forall z | z in PostSeqExcluding(t,rp) :: z >= x)
{
    if t == BSTEmpty
    {
        r, rp := BSTEmpty, [];
    }
    else if RootValue(t) >= x
    {
        r, rp := SearchLastLTSimpleRecursive(Left(t),x);
        ExtendTreePartitions(t,[0]+rp);
        rp := [0]+rp;
    }
    else
    {
        r, rp := SearchLastLTSimpleRecursive(Right(t),x);
        ExtendTreePartitions(t,[1]+rp);
        if r == BSTEmpty { r, rp := t, []; }
        else             { rp := [1]+rp;   }
    }
}

method SearchLastLESimpleRecursive( t: BST, x: int ) returns ( r: BST, ghost rp: seq<dir> )
    decreases t
	requires TreeIsSorted(t)
    ensures IsTreePath(t,rp)
    ensures r == BSTEmpty ==>
        (forall z | z in TreeSeq(t) :: z > x)
	ensures r != BSTEmpty ==>
        IsTreePath(t,rp) &&
        r == Subtree(t,rp) &&
        (forall z | z in PreSeqIncluding(t,rp) :: z <= x) &&
        (forall z | z in PostSeqExcluding(t,rp) :: z > x)
{
    if t == BSTEmpty
    {
        r, rp := BSTEmpty, [];
    }
    else if RootValue(t) > x
    {
        r, rp := SearchLastLESimpleRecursive(Left(t),x);
        ExtendTreePartitions(t,[0]+rp);
        rp := [0]+rp;
    }
    else
    {
        r, rp := SearchLastLESimpleRecursive(Right(t),x);
        ExtendTreePartitions(t,[1]+rp);
        if r == BSTEmpty { r, rp := t, []; }
        else             { rp := [1]+rp;   }
    }
}

method SearchFirstGESimpleRecursive( t: BST, x: int ) returns ( r: BST, ghost rp: seq<dir> )
    decreases t
	requires TreeIsSorted(t)
    ensures IsTreePath(t,rp)
    ensures r == BSTEmpty ==>
        (forall z | z in TreeSeq(t) :: z < x)
	ensures r != BSTEmpty ==>
        IsTreePath(t,rp) &&
        r == Subtree(t,rp) &&
        (forall z | z in PreSeqExcluding(t,rp) :: z < x) &&
        (forall z | z in PostSeqIncluding(t,rp) :: z >= x)
{
    if t == BSTEmpty
    {
        r, rp := BSTEmpty, [];
    }
    else if RootValue(t) >= x
    {
        r, rp := SearchFirstGESimpleRecursive(Left(t),x);
        ExtendTreePartitions(t,[0]+rp);
        if r == BSTEmpty { r, rp := t, []; }
        else             { rp := [0]+rp;   }
    }
    else
    {
        r, rp := SearchFirstGESimpleRecursive(Right(t),x);
        ExtendTreePartitions(t,[1]+rp);
        rp := [1]+rp;
    }
}

method SearchEQRecursive( t: BST, x: int ) returns( r: BST, ghost p: seq<dir> )
    decreases t
    requires TreeIsSorted(t)
    ensures IsTreePath(t,p)
    ensures forall z | z in PreSeq(t,p) :: z < x
    ensures forall z | z in PostSeq(t,p) :: z > x
    ensures r == Subtree(t,p)
    ensures r == BSTEmpty ==> forall z | z in TreeSeq(t) :: z != x
    ensures r != BSTEmpty ==> RootValue(r) == x
{
    if t == BSTEmpty || RootValue(t) == x { return t,[]; }
    if RootValue(t) < x 
    {
        r,p := SearchEQRecursive(Right(t),x);
        p := [1]+p;
    }
    else
    {
        r,p := SearchEQRecursive(Left(t),x);
        p := [0]+p;
    }
}

method SearchEQLoop( t: BST, x: int ) returns( r: BST, ghost p: seq<dir> )
    decreases t
    requires TreeIsSorted(t)
    ensures IsTreePath(t,p)
    ensures forall z | z in PreSeq(t,p) :: z < x
    ensures forall z | z in PostSeq(t,p) :: z > x
    ensures r == Subtree(t,p)
    ensures r == BSTEmpty ==> forall z | z in TreeSeq(t) :: z != x
    ensures r != BSTEmpty ==> RootValue(r) == x
{
    r,p := t,[];
    while r != BSTEmpty && RootValue(r) != x
        decreases r
        invariant IsTreePath(t,p)
        invariant r == Subtree(t,p)
        invariant forall z | z in PreSeq(t,p) :: z < x
        invariant forall z | z in PostSeq(t,p) :: z > x
    {
        TreePartitions(t,p);
        ExtendTreePath(t,p);
        if RootValue(r) > x
        {
            r,p := Left(r),p+[0];
        }
        else
        {
            r,p := Right(r),p+[1];
        }
    }
    TreePartitions(t,p);
}

method SearchBetweenSimpleRecursive( t: BST, x: int, y: int ) returns ( r: BST )
    decreases t
	requires TreeIsSorted(t)
    requires x <= y
    ensures IsSubTree(t,r)
    ensures r == BSTEmpty ==> forall z | z in TreeSeq(t) :: z < x || z > y
	ensures r != BSTEmpty ==> x <= RootValue(r) <= y
{
    if t == BSTEmpty || x <= RootValue(t) <= y { return t; }
    if RootValue(t) < x
    {
        r := SearchBetweenSimpleRecursive(Right(t),x,y);
    }
    else 
    {
        r := SearchBetweenSimpleRecursive(Left(t),x,y);
    }
}

method SearchBetweenSimpleLoop( t: BST, x: int, y: int ) returns ( r: BST )
	requires TreeIsSorted(t)
    requires x <= y
    ensures IsSubTree(t,r)
    ensures r == BSTEmpty ==> forall z | z in TreeSeq(t) :: z < x || z > y
	ensures r != BSTEmpty ==> x <= RootValue(r) <= y
{
    r := t;
    var rp: seq<dir> := [];
    while r != BSTEmpty
        decreases r
        invariant IsTreePath(t,rp)
        invariant r == Subtree(t,rp)
        invariant forall z | z in PreSeq(t,rp) :: z < x
        invariant forall z | z in PostSeq(t,rp) :: z > y
    {
        TreePartitions(t,rp);
        ExtendTreePath(t,rp);
        if x <= RootValue(r) <= y { return; }
        if RootValue(r) < x { r, rp := Right(r), rp+[1]; }
        else                { r, rp := Left(r), rp+[0];  }
    }
    TreePartitions(t,rp);
}

method SearchFirstGTSimpleRecursive( t: BST, x: int ) returns ( r: BST, rp: seq<dir> )
    decreases t
	requires TreeIsSorted(t)
    ensures IsTreePath(t,rp)
    ensures r == BSTEmpty ==>
        (forall z | z in TreeSeq(t) :: z <= x)
	ensures r != BSTEmpty ==>
        IsTreePath(t,rp) &&
        r == Subtree(t,rp) &&
        (forall z | z in PreSeqExcluding(t,rp) :: z <= x) &&
        (forall z | z in PostSeqIncluding(t,rp) :: z > x)
{
    if t == BSTEmpty { return BSTEmpty, []; }
    if RootValue(t) > x
    {
        r, rp := SearchFirstGTSimpleRecursive(Left(t),x);
        ExtendTreePartitions(t,[0]+rp);
        if r == BSTEmpty { r, rp := t, []; }
        else             { rp := [0]+rp;   }
    }
    else
    {
        r, rp := SearchFirstGTSimpleRecursive(Right(t),x);
        ExtendTreePartitions(t,[1]+rp);
        rp := [1]+rp;
    }
}

method SearchLEGTLoop( t: BST, x: int )
        returns ( rLE: BST
                , ghost rLEp: seq<dir>
                , rGT: BST
                , ghost rGTp: seq<dir>
                , ghost p: seq<dir> 
                )
	requires TreeIsSorted(t)
    ensures IsTreePath(t,p)
    ensures Subtree(t,p) == BSTEmpty
    ensures forall u | u in PreSeq(t,p) :: u <= x
    ensures forall u | u in PostSeq(t,p) :: u > x
    ensures rLE != BSTEmpty ==> IsTreePath(t,rLEp)
    ensures rLE != BSTEmpty ==> Subtree(t,rLEp) == rLE
    ensures rLE != BSTEmpty ==> forall u | u in PreSeqIncluding(t,rLEp) :: u <= x
    ensures rLE != BSTEmpty ==> PreSeq(t,p) == PreSeqIncluding(t,rLEp)
    ensures rLE == BSTEmpty ==> forall u | u in TreeSeq(t) :: u > x
    ensures rGT != BSTEmpty ==> IsTreePath(t,rGTp)
    ensures rGT != BSTEmpty ==> Subtree(t,rGTp) == rGT
    ensures rGT != BSTEmpty ==> forall u | u in PostSeqIncluding(t,rGTp) :: u > x
    ensures rGT != BSTEmpty ==> PostSeq(t,p) == PostSeqIncluding(t,rGTp)
    ensures rGT == BSTEmpty ==> forall u | u in TreeSeq(t) :: u <= x
{
    var s := t;
    p, rLE, rLEp, rGT, rGTp := [], BSTEmpty, [], BSTEmpty, [];
    while s != BSTEmpty
        decreases s 
        invariant TreeIsSorted(s)
        invariant IsTreePath(t,p)
        invariant s == Subtree(t,p)
        invariant PreSeq(t,p) != [] ==>
            rLE != BSTEmpty && 
            IsTreePath(t,rLEp) &&
            rLE == Subtree(t,rLEp) &&
            PreSeq(t,p) == PreSeqIncluding(t,rLEp) &&
            forall u | u in PreSeq(t,p) :: u <= x
        invariant PreSeq(t,p) == [] ==> rLE == BSTEmpty
        invariant PostSeq(t,p) != [] ==>
            rGT != BSTEmpty && 
            IsTreePath(t,rGTp) &&
            rGT == Subtree(t,rGTp) &&
            PostSeq(t,p) == PostSeqIncluding(t,rGTp) &&
            forall u | u in PostSeq(t,p) :: u > x
        invariant PostSeq(t,p) == [] ==> rGT == BSTEmpty
    {
        ExtendTreePath(t,p);
        if RootValue(s) <= x
        {
            rLE := s;
            rLEp := p;
            s := Right(s);
            p := p+[1];
        }
        else
        {
            rGT := s;
            rGTp := p;
            s := Left(s);
            p := p+[0];
        }
    }
    TreePartitions(t,p);
}

method SearchLEGTSimpleRecursive( t: BST, x: int )
        returns ( rLE: BST, ghost rLEp: seq<dir>, rGT: BST, ghost rGTp: seq<dir> )
    decreases t
	requires TreeIsSorted(t)
    ensures IsTreePath(t,rLEp) && IsTreePath(t,rGTp)
    ensures rLE == Subtree(t,rLEp) && rGT == Subtree(t,rGTp)
    ensures rLE == BSTEmpty ==>
        (forall z | z in TreeSeq(t) :: z > x)
	ensures rLE != BSTEmpty ==>
        (forall z | z in PreSeqIncluding(t,rLEp) :: z <= x) &&
        (forall z | z in PostSeqExcluding(t,rLEp) :: z > x)
    ensures rGT == BSTEmpty ==>
        (forall z | z in TreeSeq(t) :: z <= x)
	ensures rGT != BSTEmpty ==>
        (forall z | z in PreSeqExcluding(t,rGTp) :: z <= x) &&
        (forall z | z in PostSeqIncluding(t,rGTp) :: z > x)
{
    if t == BSTEmpty { return BSTEmpty, [], BSTEmpty, []; }
    if RootValue(t) > x
    {
        rLE, rLEp, rGT, rGTp := SearchLEGTSimpleRecursive(Left(t),x);
        ExtendTreePartitions(t,[0]+rLEp);
        ExtendTreePartitions(t,[0]+rGTp);
        rLEp := [0]+rLEp;
        if rGT == BSTEmpty { rGT, rGTp := t, []; }
        else               { rGTp := [0]+rGTp;   }
    }
    else
    {
        rLE, rLEp, rGT, rGTp := SearchLEGTSimpleRecursive(Right(t),x);
        ExtendTreePartitions(t,[1]+rLEp);
        ExtendTreePartitions(t,[1]+rGTp);
        rGTp := [1]+rGTp;
        if rLE == BSTEmpty { rLE, rLEp := t, []; }
        else               { rLEp := [1]+rLEp;   }
    }
}

method SearchLEGTTailRecursive  ( ghost orgt: BST
                                , t: BST
                                , ghost p: seq<dir>
                                , x: int
                                , rLEc: BST
                                , ghost rLEcp: seq<dir>
                                , rGTc: BST
                                , ghost rGTcp: seq<dir>
                                )
        returns ( rLE: BST
                , ghost rLEp: seq<dir>
                , rGT: BST
                , ghost rGTp: seq<dir>
                , ghost endp: seq<dir> 
                )
    decreases t
    requires TreeIsSorted(orgt)
    requires IsTreePath(orgt,p)
    requires t == Subtree(orgt,p)
	requires TreeIsSorted(t)
    requires rLEc != BSTEmpty ==>
        IsTreePath(orgt,rLEcp) &&
        rLEc == Subtree(orgt,rLEcp) &&
        PreSeqIncluding(orgt,rLEcp) == PreSeq(orgt,p)
    requires rGTc != BSTEmpty ==>
        IsTreePath(orgt,rGTcp) &&
        rGTc == Subtree(orgt,rGTcp) &&
        PostSeqIncluding(orgt,rGTcp) == PostSeq(orgt,p)
    requires forall z | z in PreSeq(orgt,p) :: z <= x
    requires forall z | z in PostSeq(orgt,p) :: z > x
    requires PreSeq(orgt,p) == [] <==> rLEc == BSTEmpty
    requires PostSeq(orgt,p) == [] <==> rGTc == BSTEmpty
    ensures IsTreePath(orgt,endp)
    ensures Subtree(orgt,endp) == BSTEmpty
    ensures rLE != BSTEmpty ==>
        IsTreePath(orgt,rLEp) &&
        rLE == Subtree(orgt,rLEp) &&
        PreSeqIncluding(orgt,rLEp) == PreSeq(orgt,endp)
    ensures rGT != BSTEmpty ==>
        IsTreePath(orgt,rGTp) &&
        rGT == Subtree(orgt,rGTp) &&
        PostSeqIncluding(orgt,rGTp) == PostSeq(orgt,endp)
    ensures rLE == BSTEmpty ==>
        (forall z | z in TreeSeq(orgt) :: z > x)
	ensures rLE != BSTEmpty ==>
        (forall z | z in PreSeqIncluding(orgt,rLEp) :: z <= x)
    ensures rGT == BSTEmpty ==>
        (forall z | z in TreeSeq(orgt) :: z <= x)
	ensures rGT != BSTEmpty ==>
        (forall z | z in PostSeqIncluding(orgt,rGTp) :: z > x)
{
    if t == BSTEmpty
    {
        TreePartitions(orgt,p);
        return rLEc, rLEcp, rGTc, rGTcp, p;
    }
    ExtendTreePath(orgt,p);
    if RootValue(t) > x
    {
        rLE, rLEp, rGT, rGTp, endp := SearchLEGTTailRecursive(orgt,Left(t),p+[0],x,rLEc,rLEcp,t,p);
    }
    else
    {
        rLE, rLEp, rGT, rGTp, endp := SearchLEGTTailRecursive(orgt,Right(t),p+[1],x,t,p,rGTc,rGTcp);
    }
}

method SearchLTGESimpleRecursive( t: BST, x: int )
        returns ( rLT: BST, ghost rLTp: seq<dir>, rGE: BST, ghost rGEp: seq<dir> )
    decreases t
	requires TreeIsSorted(t)
    ensures IsTreePath(t,rLTp) && IsTreePath(t,rGEp)
    ensures rLT == Subtree(t,rLTp) && rGE == Subtree(t,rGEp)
    ensures rLT == BSTEmpty ==>
        (forall z | z in TreeSeq(t) :: z >= x)
	ensures rLT != BSTEmpty ==>
        (forall z | z in PreSeqIncluding(t,rLTp) :: z < x) &&
        (forall z | z in PostSeqExcluding(t,rLTp) :: z >= x)
    ensures rGE == BSTEmpty ==>
        (forall z | z in TreeSeq(t) :: z < x)
	ensures rGE != BSTEmpty ==>
        (forall z | z in PreSeqExcluding(t,rGEp) :: z < x) &&
        (forall z | z in PostSeqIncluding(t,rGEp) :: z >= x)
{
    if t == BSTEmpty { return BSTEmpty, [], BSTEmpty, []; }
    if RootValue(t) >= x
    {
        rLT, rLTp, rGE, rGEp := SearchLTGESimpleRecursive(Left(t),x);
        ExtendTreePartitions(t,[0]+rLTp);
        ExtendTreePartitions(t,[0]+rGEp);
        rLTp := [0]+rLTp;
        if rGE == BSTEmpty { rGE, rGEp := t, []; }
        else               { rGEp := [0]+rGEp;   }
    }
    else
    {
        rLT, rLTp, rGE, rGEp := SearchLTGESimpleRecursive(Right(t),x);
        ExtendTreePartitions(t,[1]+rLTp);
        ExtendTreePartitions(t,[1]+rGEp);
        rGEp := [1]+rGEp;
        if rLT == BSTEmpty { rLT, rLTp := t, []; }
        else               { rLTp := [1]+rLTp;   }
    }
}

function CountEQSeq( s: seq<int>, x: int ): int
{
    if s == [] then
        0
    else if s[0] == x then
        1+CountEQSeq(s[1..],x)
    else
        CountEQSeq(s[1..],x)
}

lemma CountingLemma1( a: seq<int>, x: int )
    requires forall z | z in a :: z != x
    ensures CountEQSeq(a,x) == 0
{
    if a == [] { return; }
    assert forall z | z in a[1..] :: z in a;
    assert forall z | z in a[1..] :: z in a && z != x;
    CountingLemma1(a[1..],x);
    assert a[0] in a && a[0] != x;
}

lemma CountingLemma2( a: seq<int>, b: seq<int>, ab: seq<int>, x: int )
    decreases |a|
    requires ab == a+b
    ensures CountEQSeq(a+b,x) == CountEQSeq(a,x)+CountEQSeq(b,x)
{
    if a == []
    {
        assert a+b == b;
        assert CountEQSeq(a,x) == 0;
        return;
    }
    CountingLemma2(a[1..],b,a[1..]+b,x);
    assert a+b == [a[0]]+a[1..]+b;
    assert a[1..]+b == (a+b)[1..];
}

method CountEQTree( t: BST, x: int ) returns ( n: int )
    decreases t
	requires TreeIsSorted(t)
    ensures n == CountEQSeq(TreeSeq(t),x)
{
    match t 
    case BSTEmpty =>
        {
            n := 0;
        }
    case BSTNode(left,val,right) =>
        {
            if val < x
            {
                n := CountEQTree(right,x);
                CountingLemma2(TreeSeq(left)+[val],TreeSeq(right),TreeSeq(t),x);
                CountingLemma1(TreeSeq(left),x);
                CountingLemma2(TreeSeq(left),[val],TreeSeq(left)+[val],x);
            }
            else if val > x
            {
                n := CountEQTree(left,x);
                CountingLemma2(TreeSeq(left),[val]+TreeSeq(right),TreeSeq(t),x);
                CountingLemma1(TreeSeq(right),x);
                CountingLemma2([val],TreeSeq(right),[val]+TreeSeq(right),x);
            }
            else
            {
                var ln := CountEQTree(left,x);
                var rn := CountEQTree(right,x);
                n := ln+rn+1;
                CountingLemma2([val],TreeSeq(right),[val]+TreeSeq(right),x);
                CountingLemma2(TreeSeq(left),[val]+TreeSeq(right),TreeSeq(t),x);
            }
        }
}