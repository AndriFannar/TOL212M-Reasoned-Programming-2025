// Author: Snorri Agnarsson, snorri@hi.is

datatype BST = BSTEmpty | BSTNode(BST,int,BST)

function TreeSeq( t: BST ): seq<int>
    decreases t
{
    match t
    case BSTEmpty =>
        []
    case BSTNode(left,val,right) =>
        TreeSeq(left)+[val]+TreeSeq(right)
}

predicate TreeIsSorted( t: BST )
    decreases t
{
    match t
    case BSTEmpty =>
        true
    case BSTNode(left,val,right) =>
        TreeIsSorted(left) &&
        TreeIsSorted(right) &&
        (forall x | x in TreeSeq(left) :: x <= val) &&
        (forall x | x in TreeSeq(right) :: x >= val)
}

predicate TreeIsSortedAccordingToMultisets( t: BST )
    decreases t
{
    match t 
    case BSTEmpty =>
        true
    case BSTNode(left,val,right) =>
        TreeIsSortedAccordingToMultisets(left) &&
        TreeIsSortedAccordingToMultisets(right) &&
        (forall z | z in multiset(TreeSeq(left)) :: z <= val) &&
        (forall z | z in multiset(TreeSeq(right)) :: z >= val)
}

lemma TreeIsSortedEqMultisetSorted( t: BST )
    decreases t
    ensures TreeIsSorted(t) ==> TreeIsSortedAccordingToMultisets(t)
    ensures TreeIsSortedAccordingToMultisets(t) ==> TreeIsSorted(t)
{
    match t 
    case BSTEmpty =>
        {}
    case BSTNode(left,val,right) =>
        {
            TreeIsSortedEqMultisetSorted(left);
            ghost var seqleft := TreeSeq(left);
            ghost var mleft := multiset(seqleft);
            assert forall z | z in seqleft :: z in mleft;
            assert forall z | z in mleft :: z in seqleft;
            TreeIsSortedEqMultisetSorted(right);
            ghost var seqright := TreeSeq(right);
            ghost var mright := multiset(seqright);
            assert forall z | z in seqright :: z in mright;
            assert forall z | z in mright :: z in seqright;
        }
}

predicate SeqIsSorted( s: seq<int> )
{
    forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
}

lemma SortedSeqImpliesSortedTree( t: BST )
    decreases t
    requires SeqIsSorted(TreeSeq(t))
    ensures TreeIsSorted(t) 
{
    match t 
    case BSTEmpty => { return; }
    case BSTNode(A,x,B) =>
    {
        assert TreeSeq(t) == TreeSeq(A)+[x]+TreeSeq(B);
        assert TreeSeq(A) == TreeSeq(t)[..|TreeSeq(A)|];
        assert TreeSeq(B) == TreeSeq(t)[|TreeSeq(A)|+1..];
        assert SeqIsSorted(TreeSeq(A));
        assert SeqIsSorted(TreeSeq(B));
        SortedSeqImpliesSortedTree(A);
        SortedSeqImpliesSortedTree(B);
        assert x == TreeSeq(t)[|TreeSeq(A)|];
        assert forall u | u in TreeSeq(A) :: u <= x;
        assert forall u | u in TreeSeq(B) :: u >= x;
    }
}

lemma SortedTreeImpliesSortedSeq( t: BST )
    decreases t
    ensures TreeIsSorted(t) ==> SeqIsSorted(TreeSeq(t))
{
    if !TreeIsSorted(t) { return; }
    match t
    case BSTEmpty =>
        {
            return;
        }
    case BSTNode(left,val,right) =>
        {
            ghost var leftseq := TreeSeq(left);
            ghost var rightseq := TreeSeq(right);
            ghost var allseq := TreeSeq(t);
            
            SortedTreeImpliesSortedSeq(left);
            SortedTreeImpliesSortedSeq(right);
            
            assert allseq == leftseq+[val]+rightseq;
            assert SeqIsSorted(leftseq);
            assert SeqIsSorted(rightseq);
            assert forall x,y | x in leftseq && y in rightseq :: x <= val <= y;

            assert forall p,q | 0 <= p < q < |leftseq| :: allseq[p] <= allseq[q];

            assert forall p,q | 0 <= p < |leftseq| && |leftseq|+1 <= q < |allseq| ::
                allseq[p] == leftseq[p] &&
                allseq[p] in leftseq &&
                allseq[q] == rightseq[q-(|leftseq|+1)] &&
                allseq[q] in rightseq;
            assert forall p,q | 0 <= p < |leftseq| && |leftseq|+1 <= q < |allseq| ::
                allseq[p] <= allseq[q];

            assert forall p,q | |leftseq|+1 <= p < q < |allseq| ::
                allseq[p] == rightseq[p-(|leftseq|+1)] &&
                allseq[q] == rightseq[q-(|leftseq|+1)] &&
                allseq[p] <= allseq[q];
            
            assert allseq[|leftseq|] == val;
            assert forall p | 0 <= p < |leftseq| :: allseq[p] in leftseq;
            assert forall p | 0 <= p < |leftseq| :: allseq[p] <= allseq[|leftseq|];

            assert forall p | |leftseq|+1 <= p < |allseq| :: allseq[p] in rightseq;
            assert forall p | |leftseq|+1 <= p < |allseq| :: allseq[p] >= allseq[|leftseq|];
        }
}

function RootValue( t: BST ): int
    requires t != BSTEmpty
{
    match t
    case BSTNode(left,val,right) => val
}

predicate IsSubTree( t: BST, r: BST )
    decreases t
{
    if r == BSTEmpty then
        true
    else
        match t
        case BSTEmpty =>
            false
        case BSTNode(left,val,right) =>
            r == t || IsSubTree(left,r) || IsSubTree(right,r)
}

method TreeSearchAnyEQ( t: BST, x: int ) returns ( r: BST )
    decreases t
    requires TreeIsSorted(t)
    ensures x in TreeSeq(t) ==> r != BSTEmpty && IsSubTree(t,r) && x == RootValue(r)
    ensures x !in TreeSeq(t) ==> r == BSTEmpty
{
    match t
    case BSTEmpty =>
        {
            r := t;
            return;
        }
    case BSTNode(left,val,right) =>
        {
            if val == x
            {
                r := t;
                return;
            }
            if x < val
            {
                assert x !in TreeSeq(right);
                r := TreeSearchAnyEQ(left,x);
                return;
            }
            else
            {
                assert x !in TreeSeq(left);
                r := TreeSearchAnyEQ(right,x);
                return;
            }
        }
}

newtype dir = x | 0 <= x <= 1

predicate IsTreePath( t: BST, p: seq<dir> )
    decreases t
{
    if p == [] then
        true
    else
        match t
        case BSTEmpty =>
            false
        case BSTNode(left,val,right) =>
            if p[0] == 0 then
                IsTreePath(left,p[1..])
            else
                IsTreePath(right,p[1..])
}

predicate IsInFrontOf( p: seq<dir>, q: seq<dir> )
{
    if p == [] then
        if q == [] then
            false
        else if q[0] == 1 then
            true
        else
            false
    else if p[0] == 0 then
        if q == [] then
            true
        else if q[0] == 0 then
            IsInFrontOf(p[1..],q[1..])

        else
            true
    else if q == [] then
        false
    else if q[0] == 1 then
        IsInFrontOf(p[1..],q[1..])
    else
        false
}

lemma LeftIsDescending( t: BST, p: seq<dir> )
    requires TreeIsSorted(t)
    requires t != BSTEmpty
    requires IsTreePath(t,p)
    requires p != []
    requires p[0] == 0
    requires Subtree(t,p) != BSTEmpty
    ensures RootValue(Subtree(t,p)) <= RootValue(t)
{
    assert RootValue(Subtree(t,p)) in MidSeq(t,p);
    assert forall z | z in TreeSeq(Left(t)) :: z <= RootValue(t);
    TreePathConcat(t,[0],p[1..]);
    assert forall z | z in MidSeq(t,[0]+p[1..]) :: z in MidSeq(t,[0]);
    assert MidSeq(t,p) == MidSeq(t,[0]+p[1..]);
    assert MidSeq(t,[0]) == TreeSeq(Left(t));
    assert forall z | z in TreeSeq(Left(t)) :: z <= RootValue(t);
    assert RootValue(Subtree(t,p)) in TreeSeq(Left(t));
}

lemma RightIsAscending( t: BST, p: seq<dir> )
    requires TreeIsSorted(t)
    requires t != BSTEmpty
    requires IsTreePath(t,p)
    requires p != []
    requires p[0] == 1
    requires Subtree(t,p) != BSTEmpty
    ensures RootValue(Subtree(t,p)) >= RootValue(t)
{
    assert RootValue(Subtree(t,p)) in MidSeq(t,p);
    assert forall z | z in TreeSeq(Right(t)) :: z >= RootValue(t);
    TreePathConcat(t,[1],p[1..]);
    assert forall z | z in MidSeq(t,[1]+p[1..]) :: z in MidSeq(t,[1]);
    assert MidSeq(t,p) == MidSeq(t,[1]+p[1..]);
    assert MidSeq(t,[1]) == TreeSeq(Right(t));
    assert forall z | z in TreeSeq(Right(t)) :: z >= RootValue(t);
    assert RootValue(Subtree(t,p)) in TreeSeq(Right(t));
}

lemma SortedInFrontImpliesNodeLE( t: BST, p: seq<dir>, q: seq<dir> )
    requires TreeIsSorted(t)
    requires IsTreePath(t,p)
    requires IsTreePath(t,q)
    requires IsInFrontOf(p,q)
    requires Subtree(t,p) != BSTEmpty
    requires Subtree(t,q) != BSTEmpty
    ensures RootValue(Subtree(t,p)) <= RootValue(Subtree(t,q))
{
    if p == []
    {
        RightIsAscending(t,q);
        return;
    }
    if q == []
    {
        LeftIsDescending(t,p);
        return;
    }
    if p[0] == 0 == q[0] { return; }
    if p[0] == 1 == q[0] { return; }
    if p[0] == 0 && q[0] == 1
    {
        LeftIsDescending(t,p);
        RightIsAscending(t,q);
        return;
    }
    assert false;
}

function Subtree( t: BST, p: seq<dir> ): BST
    decreases t
    requires IsTreePath(t,p)
    ensures Subtree(t,p) != BSTEmpty ==> IsSubTree(t,Subtree(t,p))
{
    if p == [] then
        t
    else if p[0] == 0 then
        Subtree(Left(t),p[1..])
    else
        Subtree(Right(t),p[1..])
}

function PreSeq( t: BST, p: seq<dir> ): seq<int>
    decreases t
    requires IsTreePath(t,p)
{
    if p == [] then
        []
    else
        match t 
        case BSTEmpty =>
            []
        case BSTNode(left,val,right) =>
            if p[0] == 0 then
                PreSeq(left,p[1..])
            else
                TreeSeq(left)+[val]+PreSeq(right,p[1..])
}

function PostSeq( t: BST, p: seq<dir> ): seq<int>
    decreases t
    requires IsTreePath(t,p)
{
    if p == [] then
        []
    else
        match t 
        case BSTEmpty =>
            []
        case BSTNode(left,val,right) =>
            if p[0] == 1 then
                PostSeq(right,p[1..])
            else
                PostSeq(left,p[1..])+[val]+TreeSeq(right)
}

function MidSeq( t: BST, p: seq<dir> ): seq<int>
    requires IsTreePath(t,p)
{
    TreeSeq(Subtree(t,p))
}

lemma SequenceConcats( t: BST, p: seq<dir> )
    decreases |p|
    requires IsTreePath(t,p)
    ensures TreeSeq(t) == PreSeq(t,p)+MidSeq(t,p)+PostSeq(t,p)
{
    if p == [] { return; }
    match t 
    case BSTEmpty =>
        {
            assert false;
        }
    case BSTNode(left,val,right) =>
        {
            if p[0] == 0
            {
                SequenceConcats(left,p[1..]);
                assert TreeSeq(left) == PreSeq(left,p[1..])+MidSeq(left,p[1..])+PostSeq(left,p[1..]);
            }
            else
            {
                SequenceConcats(right,p[1..]);
                assert TreeSeq(right) == PreSeq(right,p[1..])+MidSeq(right,p[1..])+PostSeq(right,p[1..]);
                assert TreeSeq(t) == PreSeq(t,p)+MidSeq(t,p)+PostSeq(t,p);
            }
        }
}

function Left( t: BST ): BST
    requires t != BSTEmpty
{
    match t 
    case BSTNode(left,val,right) => left
}

function Right( t: BST ): BST
    requires t != BSTEmpty
{
    match t 
    case BSTNode(left,val,right) => right
}

function PreSeqExcluding( t: BST, p: seq<dir> ): seq<int>
    requires IsTreePath(t,p)
    requires Subtree(t,p) != BSTEmpty
{
    PreSeq(t,p)+TreeSeq(Left(Subtree(t,p)))
}

function PostSeqExcluding( t: BST, p: seq<dir> ): seq<int>
    requires IsTreePath(t,p)
    requires Subtree(t,p) != BSTEmpty
{
    TreeSeq(Right(Subtree(t,p)))+PostSeq(t,p)
}

function PreSeqIncluding( t: BST, p: seq<dir> ): seq<int>
    requires IsTreePath(t,p)
    requires Subtree(t,p) != BSTEmpty
{
    PreSeq(t,p)+TreeSeq(Left(Subtree(t,p)))+[RootValue(Subtree(t,p))]
}

function PostSeqIncluding( t: BST, p: seq<dir> ): seq<int>
    requires IsTreePath(t,p)
    requires Subtree(t,p) != BSTEmpty
{
    [RootValue(Subtree(t,p))]+TreeSeq(Right(Subtree(t,p)))+PostSeq(t,p)
}

lemma TreePathConcat1( t: BST, p: seq<dir>, q: seq<dir> )
    decreases |p|
    requires IsTreePath(t,p+q)
    ensures IsTreePath(t,p)
    ensures IsTreePath(Subtree(t,p),q)
    ensures Subtree(t,p+q) == Subtree(Subtree(t,p),q)
{
    if p == []
    {
        assert p+q == q;
    }
    else if p == [0]
    {
        assert Subtree(t,p) == Left(t);
        assert IsTreePath(Subtree(t,p),q);
    }
    else if p == [1]
    {
        assert Subtree(t,p) == Right(t);
        assert IsTreePath(Subtree(t,p),q);
    }
    else
    {
        assert |p| >= 2;
        if p[0] == 0
        {
            assert p+q == [0]+p[1..]+q;
            assert (p+q)[1..] == p[1..]+q;
            assert IsTreePath(Left(t),p[1..]+q);
            TreePathConcat1(Left(t),p[1..],q);
            TreePathConcat1(t,[0],p[1..]);
        }
        else
        {
            assert p+q == [1]+p[1..]+q;
            assert (p+q)[1..] == p[1..]+q;
            assert IsTreePath(Right(t),p[1..]+q);
            TreePathConcat1(Right(t),p[1..],q);
            TreePathConcat1(t,[1],p[1..]);
        }
    }
}

lemma TreePathConcat2( t: BST, p: seq<dir>, q: seq<dir> )
    decreases |p|+2*|q|
    requires IsTreePath(t,p)
    requires IsTreePath(Subtree(t,p),q)
    ensures IsTreePath(t,p+q)
    ensures Subtree(t,p+q) == Subtree(Subtree(t,p),q)
    ensures forall z | z in MidSeq(t,p+q) :: z in MidSeq(t,p)
{
    if p == []
    {
        assert p+q == q;
        SequenceConcats(t,q);
    }
    else if p == [0]
    {
        ghost var left := Left(t);
        assert Subtree(t,p) == left;
        assert IsTreePath(left,q);
        assert IsTreePath(t,p+q);
        assert MidSeq(t,p) == TreeSeq(left);
        SequenceConcats(left,q);
        assert TreeSeq(left) == PreSeq(left,q)+MidSeq(left,q)+PostSeq(left,q);
    }
    else if p == [1]
    {
        ghost var right := Right(t);
        assert Subtree(t,p) == right;
        assert IsTreePath(right,q);
        assert IsTreePath(t,p+q);
        assert MidSeq(t,p) == TreeSeq(right);
        SequenceConcats(right,q);
        assert TreeSeq(right) == PreSeq(right,q)+MidSeq(right,q)+PostSeq(right,q);
    }
    else if p[0] == 0
    {
        ghost var left := Left(t);
        TreePathConcat2(left,p[1..],q);
        assert IsTreePath(left,p[1..]+q);
        ShortenedPathConcat(p,q);
        assert p == p[0..1]+p[1..];
        assert (p+q)[0] == 0;
        assert p+q == [0]+(p+q)[1..];
        assert IsTreePath(t,p+q);
        assert Subtree(t,p+q) == Subtree(Subtree(t,p),q);
        assert MidSeq(t,p+q) == MidSeq(left,(p+q)[1..]);
        assert MidSeq(t,p) == MidSeq(left,p[1..]);
    }
    else
    {
        ghost var right := Right(t);
        TreePathConcat2(right,p[1..],q);
        assert IsTreePath(right,p[1..]+q);
        ShortenedPathConcat(p,q);
        assert p+q == [1]+(p+q)[1..];
        assert IsTreePath(t,p+q);
        assert Subtree(t,p+q) == Subtree(Subtree(t,p),q);
        assert MidSeq(t,p+q) == MidSeq(right,(p+q)[1..]);
        assert MidSeq(t,p) == MidSeq(right,p[1..]);
    }
}

lemma ShortenedPathConcat( p: seq<dir>, q: seq<dir> )
    decreases p
    ensures p != [] ==> p[1..]+q == (p+q)[1..]
{
    if p == [] { return; }
    ShortenedPathConcat(p[1..],q);
}

lemma TreePathConcat( t: BST, p: seq<dir>, q: seq<dir> )
    ensures IsTreePath(t,p+q) ==>
                IsTreePath(t,p) &&
                IsTreePath(Subtree(t,p),q) &&
                Subtree(t,p+q) == Subtree(Subtree(t,p),q) &&
                forall z | z in MidSeq(t,p+q) :: z in MidSeq(t,p)
    ensures IsTreePath(t,p) && IsTreePath(Subtree(t,p),q) ==>
                IsTreePath(t,p+q) &&
                Subtree(t,p+q) == Subtree(Subtree(t,p),q) &&
                forall z | z in MidSeq(t,p+q) :: z in MidSeq(t,p)
{
    if IsTreePath(t,p+q)
    {
        TreePathConcat1(t,p,q);
    }
    if( IsTreePath(t,p) && IsTreePath(Subtree(t,p),q) )
    {
        TreePathConcat2(t,p,q);
        assert forall z | z in MidSeq(t,p+q) :: z in MidSeq(t,p);
    }
}

lemma ExtendTreePath( t: BST, p: seq<dir> )
    decreases p
    ensures IsTreePath(t,p) && Subtree(t,p) != BSTEmpty ==>
            ( IsTreePath(t,p+[0]) &&
              Subtree(t,p+[0]) == Left(Subtree(t,p)) &&
              IsTreePath(t,p+[1]) &&
              Subtree(t,p+[1]) == Right(Subtree(t,p)) &&
              PostSeq(t,p) == PostSeq(t,p+[1]) &&
              PreSeq(t,p) == PreSeq(t,p+[0]) &&
              PreSeq(t,p+[1]) == PreSeqIncluding(t,p) &&
              PostSeq(t,p) == PostSeq(t,p+[1]) &&
              PostSeq(t,p+[0]) == PostSeqIncluding(t,p)
            )
{
    if !IsTreePath(t,p) || Subtree(t,p) == BSTEmpty
    {
        return;
    }
    if p == []
    {
        assert PostSeq(t,p) == PostSeq(t,p+[1]);
        assert PostSeq(t,p+[0]) == PostSeqIncluding(t,p);
        assert PreSeq(t,p) == PreSeq(t,p+[0]);
        assert PreSeq(t,p+[1]) == PreSeqIncluding(t,p);
        assert Subtree(t,p+[0]) == Left(Subtree(t,p));
        assert Subtree(t,p+[1]) == Right(Subtree(t,p));
        return;
    }
    assert IsTreePath(Subtree(t,p),[0]);
    assert IsTreePath(Subtree(t,p),[1]);
    TreePathConcat2(t,p,[0]);
    TreePathConcat2(t,p,[1]);
    assert IsTreePath(t,p+[0]);
    assert IsTreePath(t,p+[1]);
    if p[0] == 0
    {
        ExtendTreePath(Left(t),p[1..]);
        assert PostSeq(t,p) == PostSeq(Left(t),p[1..])+[RootValue(t)]+TreeSeq(Right(t));
        assert PostSeq(Left(t),p[1..]) == PostSeq(Left(t),p[1..]+[1]);
        assert p[1..]+[1] == (p+[1])[1..];
        assert PostSeq(t,p) == PostSeq(Left(t),(p+[1])[1..])+[RootValue(t)]+TreeSeq(Right(t));
        assert PostSeq(t,p+[1]) == PostSeq(Left(t),(p+[1])[1..])+[RootValue(t)]+TreeSeq(Right(t));
        assert PostSeq(t,p) == PostSeq(t,p+[1]);
        assert PreSeq(t,p) == PreSeq(Left(t),p[1..]);
        assert PreSeq(Left(t),p[1..]) == PreSeq(Left(t),p[1..]+[0]);
        assert p[1..]+[0] == (p+[0])[1..];
        assert PreSeq(t,p) == PreSeq(t,p+[0]);
        return;
    }
    else
    {
        ExtendTreePath(Right(t),p[1..]);
        calc == 
        {
            PostSeq(t,p+[1]);
            assert p == [1]+p[1..];
            PostSeq(t,[1]+p[1..]+[1]);
            assert [1]+p[1..]+[1] == [1]+(p[1..]+[1]);
            PostSeq(t,[1]+(p[1..]+[1]));
            PostSeq(Right(t),p[1..]+[1]);
            PostSeq(t,p);
        }
        calc ==
        {
            PreSeq(t,p+[0]);
            assert p+[0] == [1]+p[1..]+[0];
            PreSeq(t,[1]+p[1..]+[0]);
            assert [1]+p[1..]+[0] == [1]+(p[1..]+[0]);
            TreeSeq(Left(t))+[RootValue(t)]+PreSeq(Right(t),p[1..]+[0]);
            PreSeq(t,p);
        }
        calc ==
        {
            PreSeq(t,p+[1]);
            assert (p+[1])[1..] == p[1..]+[1];
            TreeSeq(Left(t))+[RootValue(t)]+PreSeq(Right(t),p[1..]+[1]);
            PreSeqIncluding(t,p);
        }
        assert (p+[0])[1..] == p[1..]+[0];
        calc ==
        {
            PostSeq(t,p+[0]);
            [RootValue(Subtree(t,p))]+TreeSeq(Right(Subtree(t,p)))+PostSeq(t,p);
            PostSeqIncluding(t,p);
        }
    }
}

lemma TreePartitions( t: BST, p: seq<dir> )
    decreases t
    requires IsTreePath(t,p)
    ensures TreeSeq(t) ==
        PreSeq(t,p)+
        MidSeq(t,p)+
        PostSeq(t,p)
    ensures Subtree(t,p) != BSTEmpty ==>
        TreeSeq(t) ==
            PreSeqExcluding(t,p)+
            PostSeqIncluding(t,p)
    ensures Subtree(t,p) != BSTEmpty ==>
        TreeSeq(t) ==
            PreSeqIncluding(t,p)+
            PostSeqExcluding(t,p)
    ensures Subtree(t,p) != BSTEmpty ==>
        RootValue(Subtree(t,p)) in TreeSeq(t) &&
        RootValue(Subtree(t,p)) in PreSeqIncluding(t,p) &&
        RootValue(Subtree(t,p)) in PostSeqIncluding(t,p)
    ensures PreSeq(t,p) <= TreeSeq(t)
    ensures Subtree(t,p) != BSTEmpty ==>
        PreSeq(t,p) <=
        PreSeqExcluding(t,p) <=
        PreSeqIncluding(t,p) <=
        TreeSeq(t)
    ensures Subtree(t,p) != BSTEmpty ==>
        RootValue(Subtree(t,p)) in TreeSeq(t) &&
        RootValue(Subtree(t,p)) in MidSeq(t,p) &&
        RootValue(Subtree(t,p)) in PostSeqIncluding(t,p) &&
        RootValue(Subtree(t,p)) in PreSeqIncluding(t,p)
    ensures (Subtree(t,p) != BSTEmpty && TreeIsSorted(t)) ==> 
        (forall z | z in PreSeq(t,p) :: z <= RootValue(Subtree(t,p))) &&
        (forall z | z in PreSeqExcluding(t,p) :: z <= RootValue(Subtree(t,p))) &&
        (forall z | z in PreSeqIncluding(t,p) :: z <= RootValue(Subtree(t,p))) &&
        (forall z | z in PostSeq(t,p) :: z >= RootValue(Subtree(t,p))) &&
        (forall z | z in PostSeqExcluding(t,p) :: z >= RootValue(Subtree(t,p))) &&
        (forall z | z in PostSeqIncluding(t,p) :: z >= RootValue(Subtree(t,p))) &&
        (forall z,w | z in PreSeq(t,p) && w in MidSeq(t,p) :: z <= w) &&
        (forall z,w | z in PreSeq(t,p) && w in PostSeq(t,p) :: z <= w) &&
        (forall z,w | z in MidSeq(t,p) && w in PostSeq(t,p) :: z <= w) && 
        (forall z,w | z in PreSeqExcluding(t,p) && w in PostSeqIncluding(t,p) :: z <= w) && 
        (forall z,w | z in PreSeqExcluding(t,p) && w in PostSeqExcluding(t,p) :: z <= w) && 
        (forall z,w | z in PreSeqIncluding(t,p) && w in PostSeqIncluding(t,p) :: z <= w) && 
        (forall z,w | z in PreSeqIncluding(t,p) && w in PostSeqExcluding(t,p) :: z <= w)
{
    if t == BSTEmpty { return; }
    if p == []
    {
        assert PreSeqExcluding(t,p) == TreeSeq(Left(t));
        assert PreSeqIncluding(t,p) == TreeSeq(Left(t))+[RootValue(t)];
        assert PostSeqExcluding(t,p) == TreeSeq(Right(t));
        assert PostSeqIncluding(t,p) == [RootValue(t)]+TreeSeq(Right(t));
        assert TreeSeq(t) ==
                PreSeqExcluding(t,p)+
                PostSeqIncluding(t,p);
        assert TreeSeq(t) ==
                PreSeqIncluding(t,p)+
                PostSeqExcluding(t,p);
        return;
    }
    else
    {
        if p[0] == 0
        {
            TreePartitions(Left(t),p[1..]);
            assert PostSeq(t,p) == PostSeq(Left(t),p[1..])+[RootValue(t)]+TreeSeq(Right(t));
            assert Subtree(t,p) == Subtree(Left(t),p[1..]);
            assert MidSeq(t,p) == MidSeq(Left(t),p[1..]);
            if Subtree(t,p) == BSTEmpty { return; }
            if !TreeIsSorted(t) { return; }
            assert forall z,w | z in MidSeq(t,p) && w in PostSeq(Left(t),p[1..]) :: z <= w;
            assert forall z | z in MidSeq(Left(t),p[1..]) :: z in TreeSeq(Left(t));
            assert forall z | z in TreeSeq(Left(t)) :: z <= RootValue(t);
            assert forall z | z in MidSeq(Left(t),p[1..]) :: z <= RootValue(t);
            assert forall z | z in MidSeq(t,p) :: z <= RootValue(t);
            assert forall z,w | z in MidSeq(t,p) && w in TreeSeq(Right(t)) :: z <= w;
            assert forall z,w | z in MidSeq(t,p) && w in PostSeq(t,p) :: z <= w;
            assert PostSeqIncluding(t,p) == PostSeqIncluding(Left(t),p[1..])+[RootValue(t)]+TreeSeq(Right(t));
            assert forall z | z in PostSeqIncluding(t,p) :: z >= RootValue(Subtree(t,p));
            assert forall z | z in PostSeqExcluding(t,p) :: z in PostSeqIncluding(t,p);
            assert forall z | z in PostSeqExcluding(t,p) :: z >= RootValue(Subtree(t,p));
            return;
        }
        else
        {
            TreePartitions(Right(t),p[1..]);
            assert PreSeq(t,p) == TreeSeq(Left(t))+[RootValue(t)]+PreSeq(Right(t),p[1..]);
            assert Subtree(t,p) == Subtree(Right(t),p[1..]);
            assert MidSeq(t,p) == MidSeq(Right(t),p[1..]);
            if Subtree(t,p) == BSTEmpty { return; }
            if !TreeIsSorted(t) { return; }
            assert PreSeqExcluding(t,p) == TreeSeq(Left(t))+[RootValue(t)]+PreSeqExcluding(Right(t),p[1..]);
            assert forall z | z in PreSeqExcluding(t,p) :: z <= RootValue(Subtree(t,p));
            assert PreSeq(t,p) == TreeSeq(Left(t))+[RootValue(t)]+PreSeq(Right(t),p[1..]);
            assert forall w | w in MidSeq(t,p) :: w in TreeSeq(Right(t));
            assert forall z,w | z in TreeSeq(Left(t)) && w in MidSeq(t,p) :: z <= w;
            assert forall z,w | z in PreSeq(t,p) && w in MidSeq(t,p) :: z <= w;
            return;
        }
    }
}

method SearchFirstGELoop( t: BST, x: int ) returns ( r: BST )
    requires TreeIsSorted(t)
    ensures (forall z | z in TreeSeq(t) :: z < x) ==>
        r == BSTEmpty
    ensures (exists z | z in TreeSeq(t) :: z >= x) ==>
        r != BSTEmpty &&
        (exists rp | IsTreePath(t,rp) ::
         r == Subtree(t,rp) &&
         (forall z | z in PreSeqExcluding(t,rp) :: z < x) &&
         (forall z | z in PostSeqIncluding(t,rp) :: z >= x)
        )
{
    ghost var p: seq<dir> := [];
    ghost var rp := p;
    var s := t;
    r := BSTEmpty;
    while s != BSTEmpty
        decreases s
        invariant IsTreePath(t,p)
        invariant s == Subtree(t,p)
        invariant forall z | z in PreSeq(t,p) :: z < x
        invariant forall z | z in PostSeq(t,p) :: z >= x
        invariant r == BSTEmpty ==>
            PostSeq(t,p) == []
        invariant r != BSTEmpty ==>
            IsTreePath(t,rp) &&
            r == Subtree(t,rp) &&
            PreSeqExcluding(t,rp) == PreSeq(t,p)+TreeSeq(s) &&
            PostSeqIncluding(t,rp) == PostSeq(t,p)
        invariant TreeIsSorted(s)
    {
        ExtendTreePath(t,p);
        if RootValue(s) >= x
        {
            r := s;
            rp := p;
            p := p+[0];
            s := Left(s);
        }
        else
        {
            p := p+[1];
            s := Right(s);
        }
    }
    TreePartitions(t,p);
    if r == BSTEmpty { return; }
    TreePartitions(t,rp);
}

method SearchFirstGERecursiveHelp   ( ghost orgt: BST
                                    , t: BST
                                    , ghost tp: seq<dir>
                                    , x: int
                                    , c: BST
                                    , ghost cp: seq<dir>
                                    )
        returns ( r: BST, ghost rp: seq<dir> )
    decreases t
    requires TreeIsSorted(orgt)
    requires IsTreePath(orgt,tp)
    requires t == Subtree(orgt,tp)
    requires forall z | z in PreSeq(orgt,tp) :: z < x
    requires forall z | z in PostSeq(orgt,tp) :: z >= x
    requires c == BSTEmpty ==>
        PostSeq(orgt,tp) == [] && cp == []
    requires c != BSTEmpty ==>
        IsTreePath(orgt,cp) &&
        c == Subtree(orgt,cp) &&
        PreSeqExcluding(orgt,cp) == PreSeq(orgt,tp)+TreeSeq(t) &&
        PostSeqIncluding(orgt,cp) == PostSeq(orgt,tp)
    requires TreeIsSorted(t)
    ensures (forall z | z in TreeSeq(orgt) :: z < x) ==>
        r == BSTEmpty && rp == []
    ensures (exists z | z in TreeSeq(orgt) :: z >= x) ==>
        r != BSTEmpty &&
        IsTreePath(orgt,rp) &&
        r == Subtree(orgt,rp) &&
        (forall z | z in PreSeqExcluding(orgt,rp) :: z < x) &&
        (forall z | z in PostSeqIncluding(orgt,rp) :: z >= x)
{
    if t == BSTEmpty
    {
        r := c;
        rp := cp;
        TreePartitions(orgt,tp);
        if r == BSTEmpty { return; }
        TreePartitions(orgt,rp);
        return;
    }
    ExtendTreePath(orgt,tp);
    if RootValue(t) < x
    {
        r,rp := SearchFirstGERecursiveHelp(orgt,Right(t),tp+[1],x,c,cp);
    }
    else
    {
        r,rp := SearchFirstGERecursiveHelp(orgt,Left(t),tp+[0],x,t,tp);
    }
}

method SearchFirstGERecursive( t: BST, x: int ) returns ( r: BST )
    requires TreeIsSorted(t)
    ensures (forall z | z in TreeSeq(t) :: z < x) ==>
        r == BSTEmpty
    ensures (exists z | z in TreeSeq(t) :: z >= x) ==>
        r != BSTEmpty &&
        (exists rp | IsTreePath(t,rp) ::
         r == Subtree(t,rp) &&
         (forall z | z in PreSeqExcluding(t,rp) :: z < x) &&
         (forall z | z in PostSeqIncluding(t,rp) :: z >= x)
        )
{
    ghost var rp: seq<dir>;
    r,rp := SearchFirstGERecursiveHelp(t,t,[],x,BSTEmpty,[]);
    if r == BSTEmpty { return; }
    TreePartitions(t,rp);
}

method SearchLastLTLoop( t: BST, x: int ) returns ( r: BST )
    requires TreeIsSorted(t)
    ensures (forall z | z in TreeSeq(t) :: z >= x) ==>
        r == BSTEmpty
    ensures (exists z | z in TreeSeq(t) :: z < x) ==>
        r != BSTEmpty &&
        (exists rp | IsTreePath(t,rp) ::
         r == Subtree(t,rp) &&
         (forall z | z in PreSeqIncluding(t,rp) :: z < x) &&
         (forall z | z in PostSeqExcluding(t,rp) :: z >= x)
        )
{
    ghost var p: seq<dir> := [];
    ghost var rp := p;
    var s := t;
    r := BSTEmpty;
    while s != BSTEmpty
        decreases s
        invariant IsTreePath(t,p)
        invariant s == Subtree(t,p)
        invariant forall z | z in PreSeq(t,p) :: z < x
        invariant forall z | z in PostSeq(t,p) :: z >= x
        invariant r == BSTEmpty ==>
            PreSeq(t,p) == []
        invariant r != BSTEmpty ==>
            IsTreePath(t,rp) &&
            r == Subtree(t,rp) &&
            PreSeqIncluding(t,rp) == PreSeq(t,p) &&
            PostSeqExcluding(t,rp) == TreeSeq(s)+PostSeq(t,p)
        invariant TreeIsSorted(s)
    {
        ExtendTreePath(t,p);
        if RootValue(s) >= x
        {
            p := p+[0];
            s := Left(s);
        }
        else
        {
            r := s;
            rp := p;
            p := p+[1];
            s := Right(s);
        }
    }
    TreePartitions(t,p);
    if r == BSTEmpty { return; }
    TreePartitions(t,rp);
}

method Insert( t: BST, x: int ) returns ( r: BST )
    decreases t
    requires TreeIsSorted(t)
    ensures TreeIsSorted(r)
    ensures multiset(TreeSeq(r)) == multiset(TreeSeq(t))+multiset{x}
    ensures forall z | z in TreeSeq(r) :: z == x || z in TreeSeq(t)
{
    if t == BSTEmpty
    {
        r := BSTNode(BSTEmpty,x,BSTEmpty);
    }
    else if x < RootValue(t)
    {
        r := Insert(Left(t),x);
        r := BSTNode(r,RootValue(t),Right(t));
    }
    else
    {
        r := Insert(Right(t),x);
        r := BSTNode(Left(t),RootValue(t),r);
    }
}

function MaxInTree( t: BST ): int
    decreases t
    requires t != BSTEmpty
    requires TreeIsSorted(t)
    ensures MaxInTree(t) in TreeSeq(t)
    ensures forall z | z in TreeSeq(t) :: z <= MaxInTree(t)
{
    match t 
    case BSTNode(left,val,right) =>
        if right == BSTEmpty then
            val
        else
            MaxInTree(right)
}

function MinInTree( t: BST ): int
    decreases t
    requires t != BSTEmpty
    requires TreeIsSorted(t)
    ensures MinInTree(t) in TreeSeq(t)
    ensures forall z | z in TreeSeq(t) :: z >= MinInTree(t)
{
    match t 
    case BSTNode(left,val,right) =>
        if left == BSTEmpty then
            val
        else
            MinInTree(left)
}

function DeleteMaxFun( t: BST ): BST
    decreases t
    requires t != BSTEmpty
    requires TreeIsSorted(t)
    ensures multiset(TreeSeq(DeleteMaxFun(t))) == multiset(TreeSeq(t))-multiset{MaxInTree(t)}
{
    match t 
    case BSTNode(left,val,right) =>
        if right == BSTEmpty then
            left
        else
            BSTNode(left,val,DeleteMaxFun(right))
}

function DeleteMinFun( t: BST ): BST
    decreases t
    requires t != BSTEmpty
    requires TreeIsSorted(t)
    ensures multiset(TreeSeq(DeleteMinFun(t))) == multiset(TreeSeq(t))-multiset{MinInTree(t)}
{
    match t 
    case BSTNode(left,val,right) =>
        if left == BSTEmpty then
            right
        else
            BSTNode(DeleteMinFun(left),val,right)
}

lemma DeletionRoot( left: BST, root: int, right: BST, newroot: int, newright: BST, t: BST, r: BST )
    requires t == BSTNode(left,root,right)
    requires r == BSTNode(left,newroot,newright)
    requires TreeIsSorted(t)
    requires TreeIsSorted(r)
    requires newroot in TreeSeq(right)
    requires forall z | z in TreeSeq(right) :: z >= newroot
    requires multiset(TreeSeq(right)) == multiset(TreeSeq(newright))+multiset{newroot}
    ensures multiset(TreeSeq(r)) == multiset(TreeSeq(t))-multiset{root}
    ensures forall z | z in TreeSeq(r) :: z in TreeSeq(t)
{
    assert multiset(TreeSeq(r)) < multiset(TreeSeq(t));
    assert forall z | z in TreeSeq(r) :: z in multiset(TreeSeq(r)) && z in multiset(TreeSeq(t)) && z in TreeSeq(t);
}

lemma DeletionLeft( left: BST, root: int, right: BST, x: int, newleft: BST, t: BST, r: BST )
    requires t == BSTNode(left,root,right)
    requires r == BSTNode(newleft,root,right)
    requires TreeIsSorted(t)
    requires TreeIsSorted(r)
    requires x < root
    requires multiset(TreeSeq(newleft)) == multiset(TreeSeq(left))-multiset{x}
    ensures multiset(TreeSeq(r)) == multiset(TreeSeq(t))-multiset{x}
    ensures forall z | z in TreeSeq(r) :: z in TreeSeq(t)
{
    assert forall z | z in TreeSeq(right) :: z >= root > x && z != x;
    if x !in TreeSeq(left)
    {
        assert x !in TreeSeq(t);
        assert multiset(TreeSeq(newleft)) == multiset(TreeSeq(left))-multiset{x} == multiset(TreeSeq(left));
        assert multiset(TreeSeq(r)) == multiset(TreeSeq(t));
        assert forall z | z in TreeSeq(r) :: z in multiset(TreeSeq(r)) &&  z in multiset(TreeSeq(t)) && z in TreeSeq(t);
        return;
    }
    var A := multiset{root}+multiset(TreeSeq(right));
    var B := multiset(TreeSeq(left));
    assert forall z | z in A :: (z==root || z in TreeSeq(right));
    assert forall z | z in A :: z >= root > x;
    assert x !in A;
    SubtractFromContainingUnion(A,B,x);
}

lemma DeletionRight( left: BST, root: int, right: BST, x: int, newright: BST, t: BST, r: BST )
    requires t == BSTNode(left,root,right)
    requires r == BSTNode(left,root,newright)
    requires TreeIsSorted(t)
    requires TreeIsSorted(r)
    requires x > root
    requires multiset(TreeSeq(newright)) == multiset(TreeSeq(right))-multiset{x}
    ensures multiset(TreeSeq(r)) == multiset(TreeSeq(t))-multiset{x}
    ensures forall z | z in TreeSeq(r) :: z in TreeSeq(t)
{
    assert forall z | z in TreeSeq(left) :: z <= root < x && z != x;
    if x !in TreeSeq(right)
    {
        assert x !in TreeSeq(t);
        assert multiset(TreeSeq(newright)) == multiset(TreeSeq(right))-multiset{x} == multiset(TreeSeq(right));
        assert multiset(TreeSeq(r)) == multiset(TreeSeq(t));
        assert forall z | z in TreeSeq(r) :: z in multiset(TreeSeq(r)) &&  z in multiset(TreeSeq(t)) && z in TreeSeq(t);
        return;
    }
    var A := multiset(TreeSeq(left))+multiset{root};
    var B := multiset(TreeSeq(right));
    assert forall z | z in A :: (z in TreeSeq(left) || z==root);
    assert forall z | z in A :: z <= root < x;
    assert x !in A;
    SubtractFromContainingUnion(A,B,x);
}

lemma SubtractFromContainingUnion( A: multiset<int>, B: multiset<int>, x: int )
    decreases A
    requires x in B
    requires x !in A
    ensures (A+B)-multiset{x} == A+(B-multiset{x})
    ensures A+B-multiset{x} == A+(B-multiset{x})
    ensures (B+A)-multiset{x} == A+(B-multiset{x})
{
    if A == multiset{} { return; }
    var z :| z in A;
    SubtractFromContainingUnion(A-multiset{z},B,x);
    assert A == (A-multiset{z})+multiset{z};
    assert A == multiset{z}+(A-multiset{z});
}

method Delete( t: BST, x: int ) returns ( r: BST )
    decreases t
    requires TreeIsSorted(t)
    ensures TreeIsSorted(r)
    ensures multiset(TreeSeq(r)) == multiset(TreeSeq(t))-multiset{x}
    ensures x !in TreeSeq(t) ==> r == t
    ensures forall z | z in TreeSeq(r) :: z in TreeSeq(t)
{
    if t == BSTEmpty { return BSTEmpty; }
    var left := Left(t);
    var root := RootValue(t);
    var right := Right(t);
    if root == x
    {
        if left == BSTEmpty  { return right; }
        if right == BSTEmpty { return left;  }
        var newright, min := DeleteMin(right);
        r := BSTNode(left,min,newright);
        DeletionRoot(left,root,right,min,newright,t,r);
    }
    else if x < root
    {
        var newleft := Delete(left,x);
        r := BSTNode(newleft,root,right);
        DeletionLeft(left,root,right,x,newleft,t,r);
    }
    else
    {
        var newright := Delete(right,x);
        r := BSTNode(Left(t),root,newright);
        DeletionRight(left,root,right,x,newright,t,r);
    }
}

method DeleteMax( t: BST ) returns ( newt: BST, max: int )
    decreases t
    requires TreeIsSorted(t)
    requires t != BSTEmpty
    ensures TreeIsSorted(newt)
    ensures multiset(TreeSeq(t)) == multiset(TreeSeq(newt))+multiset{max}
    ensures max in TreeSeq(t)
    ensures max == TreeSeq(t)[|TreeSeq(t)|-1]
    ensures max == MaxInTree(t)
    ensures newt == DeleteMaxFun(t)
    ensures forall z | z in TreeSeq(newt) :: z in TreeSeq(t)
    ensures forall z | z in TreeSeq(t) :: max >= z
{
    if Right(t) == BSTEmpty
    {
        max := RootValue(t);
        assert max == TreeSeq(t)[|TreeSeq(t)|-1];
        newt := Left(t);
        return;
    }
    newt, max := DeleteMax(Right(t));
    assert max == TreeSeq(Right(t))[|TreeSeq(Right(t))|-1];
    newt := BSTNode(Left(t),RootValue(t),newt);
}

method DeleteMin( t: BST ) returns ( newt: BST, min: int )
    decreases t
    requires TreeIsSorted(t)
    requires t != BSTEmpty
    ensures TreeIsSorted(newt)
    ensures multiset(TreeSeq(t)) == multiset(TreeSeq(newt))+multiset{min}
    ensures min in TreeSeq(t)
    ensures min == TreeSeq(t)[0]
    ensures min == MinInTree(t)
    ensures newt == DeleteMinFun(t)
    ensures forall z | z in TreeSeq(t) :: min <= z
    ensures forall z | z in TreeSeq(newt) :: z in TreeSeq(t)
{
    if Left(t) == BSTEmpty
    {
        min := RootValue(t);
        assert min == TreeSeq(t)[0];
        newt := Right(t);
        return;
    }
    newt, min := DeleteMin(Left(t));
    assert min == TreeSeq(Left(t))[0];
    newt := BSTNode(newt,RootValue(t),Right(t));
}

lemma RecursionSearchLemma()
    ensures forall t: BST, p: seq<dir> |
        IsTreePath(t,p) && p != [] && p[0]==0 && Subtree(t,p) != BSTEmpty ::
        PreSeqExcluding(t,p) == PreSeqExcluding(Left(t),p[1..]) &&
        PreSeqIncluding(t,p) == PreSeqIncluding(Left(t),p[1..]) &&
        PostSeqExcluding(t,p) == PostSeqExcluding(Left(t),p[1..])+[RootValue(t)]+TreeSeq(Right(t)) &&
        PostSeqIncluding(t,p) == PostSeqIncluding(Left(t),p[1..])+[RootValue(t)]+TreeSeq(Right(t))
    ensures forall t: BST, p: seq<dir> |
        IsTreePath(t,p) && p != [] && p[0]==1 && Subtree(t,p) != BSTEmpty ::
        PostSeqExcluding(t,p) == PostSeqExcluding(Right(t),p[1..]) &&
        PostSeqIncluding(t,p) == PostSeqIncluding(Right(t),p[1..]) &&
        PreSeqExcluding(t,p) == TreeSeq(Left(t))+[RootValue(t)]+PreSeqExcluding(Right(t),p[1..]) &&
        PreSeqIncluding(t,p) == TreeSeq(Left(t))+[RootValue(t)]+PreSeqIncluding(Right(t),p[1..])
{}

lemma ExtendTreePartitions( t: BST, p: seq<dir> )
    requires IsTreePath(t,p)
    requires p != []
    ensures p[0]==0 && Subtree(t,p) != BSTEmpty ==>
        PreSeqExcluding(t,p) == PreSeqExcluding(Left(t),p[1..])
    ensures p[0]==0 && Subtree(t,p) != BSTEmpty ==>
        PreSeqIncluding(t,p) == PreSeqIncluding(Left(t),p[1..])
    ensures p[0]==0 && Subtree(t,p) != BSTEmpty ==>
        PostSeqExcluding(t,p) == PostSeqExcluding(Left(t),p[1..])+[RootValue(t)]+TreeSeq(Right(t))
    ensures p[0]==0 && Subtree(t,p) != BSTEmpty ==>
        PostSeqIncluding(t,p) == PostSeqIncluding(Left(t),p[1..])+[RootValue(t)]+TreeSeq(Right(t))
    ensures p[0]==1 && Subtree(t,p) != BSTEmpty ==>
        PreSeqExcluding(t,p) == TreeSeq(Left(t))+[RootValue(t)]+PreSeqExcluding(Right(t),p[1..])
    ensures p[0]==1 && Subtree(t,p) != BSTEmpty ==>
        PreSeqIncluding(t,p) == TreeSeq(Left(t))+[RootValue(t)]+PreSeqIncluding(Right(t),p[1..])
    ensures p[0]==1 && Subtree(t,p) != BSTEmpty ==>
        PostSeqExcluding(t,p) == PostSeqExcluding(Right(t),p[1..])
    ensures p[0]==1 && Subtree(t,p) != BSTEmpty ==>
        PostSeqIncluding(t,p) == PostSeqIncluding(Right(t),p[1..])
{}

lemma RelateSeqs( t: BST, p: seq<dir> )
	requires IsTreePath(t,p)
	requires Subtree(t,p) != BSTEmpty
	ensures PreSeqExcluding(t,p) == PreSeq(t,p)+TreeSeq(Left(Subtree(t,p)))
	ensures PreSeqIncluding(t,p) == PreSeqExcluding(t,p)+[RootValue(Subtree(t,p))]
	ensures PostSeqExcluding(t,p) == TreeSeq(Right(Subtree(t,p)))+PostSeq(t,p)
	ensures PostSeqIncluding(t,p) == [RootValue(Subtree(t,p))]+PostSeqExcluding(t,p)
{}