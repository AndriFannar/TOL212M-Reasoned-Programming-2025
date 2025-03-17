include "BST.dfy"

// Instead of using the above "include" line you can remove that line
// and use the following command to build this file:
//  dafny build Splay.dfy --library:BST.doo

function Zig( t: BST ): BST
    requires t != BSTEmpty
    requires Left(t) != BSTEmpty
    ensures TreeSeq(Zig(t)) == TreeSeq(t)
    ensures Right(Zig(t)) != BSTEmpty
    ensures Left(Zig(t)) == Left(Left(t))
    ensures Left(Right(Zig(t))) == Right(Left(t))
    ensures Right(Right(Zig(t))) == Right(t)
    ensures RootValue(Zig(t)) == RootValue(Left(t))
{
    match t 
    case BSTNode(BSTNode(A,x,B),y,C) => BSTNode(A,x,BSTNode(B,y,C))
}

function Zag( t: BST ): BST
    requires t != BSTEmpty
    requires Right(t) != BSTEmpty
    ensures TreeSeq(Zag(t)) == TreeSeq(t)
    ensures Left(Zag(t)) != BSTEmpty
    ensures Right(Zag(t)) == Right(Right(t))
    ensures RootValue(Zag(t)) == RootValue(Right(t))
{
    match t 
    case BSTNode(A,x,BSTNode(B,y,C)) => BSTNode(BSTNode(A,x,B),y,C)
}

lemma ZagLiftsRight( t: BST )
    requires t != BSTEmpty
    requires Right(t) != BSTEmpty
    ensures PreSeqExcluding(t,[1]) == PreSeqExcluding(Zag(t),[])
    ensures PostSeqIncluding(t,[1]) == PostSeqIncluding(Zag(t),[])
{
    match t 
    case BSTNode(A,x,BSTNode(B,y,C)) => 
    {
        assert Right(t) == Subtree(t,[1]) == BSTNode(B,y,C);
        calc ==
        {
            PreSeqExcluding(t,[1]);
            TreeSeq(A)+[x]+PreSeqExcluding(BSTNode(B,y,C),[]);
            TreeSeq(A)+[x]+TreeSeq(B);
        }
        calc ==
        {
            PostSeqIncluding(t,[1]);
            [y]+PostSeqExcluding(t,[1]);
            [y]+PostSeqExcluding(BSTNode(B,y,C),[]);
            [y]+TreeSeq(C);
        }
    }
}

lemma ZigLiftsLeft( t: BST )
    requires t != BSTEmpty
    requires Left(t) != BSTEmpty
    ensures PreSeqExcluding(t,[0]) == PreSeqExcluding(Zig(t),[])
    ensures PostSeqIncluding(t,[0]) == PostSeqIncluding(Zig(t),[])
{
    match t 
    case BSTNode(BSTNode(A,x,B),y,C) => 
    {
        assert Left(t) == Subtree(t,[0]) == BSTNode(A,x,B);
        calc ==
        {
            PreSeqExcluding(t,[0]);
            PreSeqExcluding(Left(t),[]);
            TreeSeq(A);
        }
        calc ==
        {
            PostSeqIncluding(t,[0]);
            [x]+PostSeqExcluding(t,[0]);
            [x]+PostSeqExcluding(t,[0]);
            [x]+PostSeqExcluding(Left(t),[])+[y]+TreeSeq(C);
        }
    }
}

function ZigZig( t: BST ): BST
    requires t != BSTEmpty
    requires Left(t) != BSTEmpty
    requires Left(Left(t)) != BSTEmpty
    ensures TreeSeq(t) == TreeSeq(ZigZig(t))
    ensures RootValue(ZigZig(t)) == RootValue(Left(Left(t)))
    ensures Left(ZigZig(t)) == Left(Left(Left(t)))
{
    Zig(Zig(t))
}

function ZagZag( t: BST ): BST
    requires t != BSTEmpty
    requires Right(t) != BSTEmpty
    requires Right(Right(t)) != BSTEmpty
    ensures TreeSeq(t) == TreeSeq(ZagZag(t))
    ensures RootValue(ZagZag(t)) == RootValue(Right(Right(t)))
    ensures Right(ZagZag(t)) == Right(Right(Right(t)))
{
    Zag(Zag(t))
}

function ZigZag( t: BST ): BST
    requires t != BSTEmpty
    requires Left(t) != BSTEmpty
    requires Right(Left(t)) != BSTEmpty
    ensures TreeSeq(t) == TreeSeq(ZigZag(t))
    ensures RootValue(ZigZag(t)) == RootValue(Right(Left(t)))
{
    match t 
    case BSTNode(A,x,B) => Zig(BSTNode(Zag(A),x,B))
}

function ZagZig( t: BST ): BST
    requires t != BSTEmpty
    requires Right(t) != BSTEmpty
    requires Left(Right(t)) != BSTEmpty
    ensures TreeSeq(t) == TreeSeq(ZagZig(t))
    ensures RootValue(ZagZig(t)) == RootValue(Left(Right(t)))
{
    match t 
    case BSTNode(A,x,B) => Zag(BSTNode(A,x,Zig(B)))
}

method SplayMin( t: BST ) returns( s: BST )
    decreases t
    ensures TreeSeq(s) == TreeSeq(t)
    ensures s == BSTEmpty || Left(s) == BSTEmpty
{
    match t 
    case BSTEmpty => { return BSTEmpty; }
    case BSTNode(left,x,right) =>
    {
        match left
        case BSTEmpty =>              { s := t;    }
        case BSTNode(BSTEmpty,_,_) => { s:=Zig(t); }
        case BSTNode(left2,y,right2) =>
        {
            var newleft2 := SplayMin(left2);
            assert TreeSeq(BSTNode(newleft2,y,right2)) == TreeSeq(BSTNode(left2,y,right2));
            s := BSTNode(BSTNode(newleft2,y,right2),x,right);
            s := ZigZig(s);
        }
    }
}

method SplayMax( t: BST ) returns( s: BST )
    decreases t
    ensures TreeSeq(s) == TreeSeq(t)
    ensures s == BSTEmpty || Right(s) == BSTEmpty
{
    match t 
    case BSTEmpty => { return BSTEmpty; }
    case BSTNode(left,x,right) =>
    {
        match right
        case BSTEmpty =>              { s := t;      }
        case BSTNode(_,_,BSTEmpty) => { s := Zag(t); }
        case BSTNode(left2,y,right2) =>
        {
            var newright2 := SplayMax(right2);
            assert TreeSeq(BSTNode(left2,y,right2)) == TreeSeq(BSTNode(left2,y,newright2));
            s := BSTNode(left,x,BSTNode(left2,y,newright2));
            s := ZagZag(s);
        }
    }
}

method SplayPath( t: BST, p: seq<dir> ) returns( s: BST )
    requires IsTreePath(t,p)
    requires Subtree(t,p) != BSTEmpty
    requires TreeIsSorted(t)
    ensures TreeSeq(t) == TreeSeq(s)
    ensures RootValue(s) == RootValue(Subtree(t,p))
    ensures TreeIsSorted(s)
{
    SortedTreeImpliesSortedSeq(t);
    assert SeqIsSorted(TreeSeq(t));
    if p==[]
    {
        s := t;
    }
    else if p==[0]
    {
        s := Zig(t);
    }
    else if p==[1]
    {
        s := Zag(t);
    }
    else if p[..2]==[0,0]
    {
        //        y
        //       / \
        //      /   \
        //     x     C
        //    / \ 
        //   A   B
        var y := RootValue(t);
        var x := RootValue(Left(t));
        var A := SplayPath(Left(Left(t)),p[2..]);
        assert TreeSeq(A) == TreeSeq(Left(Left(t)));
        var B := Right(Left(t));
        var C := Right(t);
        assert TreeSeq(t) == TreeSeq(A)+[x]+TreeSeq(B)+[y]+TreeSeq(C);
        var s' := BSTNode(BSTNode(A,x,B),y,C);
        assert TreeSeq(s') == TreeSeq(A)+[x]+TreeSeq(B)+[y]+TreeSeq(C);
        s := ZigZig(s');
        assert TreeSeq(s) == TreeSeq(s');
    }
    else if p[..2]==[0,1]
    {
        //        y
        //       / \
        //      /   \
        //     x     C
        //    / \ 
        //   A   B
        var y := RootValue(t);
        var x := RootValue(Left(t));
        var A := Left(Left(t));
        var B := SplayPath(Right(Left(t)),p[2..]);
        assert TreeSeq(B) == TreeSeq(Right(Left(t)));
        var C := Right(t);
        assert TreeSeq(t) == TreeSeq(A)+[x]+TreeSeq(B)+[y]+TreeSeq(C);
        var s' := BSTNode(BSTNode(A,x,B),y,C);
        assert TreeSeq(s') == TreeSeq(A)+[x]+TreeSeq(B)+[y]+TreeSeq(C);
        s := ZigZag(s');
        assert TreeSeq(s) == TreeSeq(s');
    }
    else if p[..2]==[1,0]
    {
        //     x
        //    / \
        //   /   \
        //  A     y
        //       / \
        //      B   C
        var x := RootValue(t);
        var A := Left(t);
        var y := RootValue(Right(t));
        var B := SplayPath(Left(Right(t)),p[2..]);
        assert TreeSeq(B) == TreeSeq(Left(Right(t)));
        var C := Right(Right(t));
        assert TreeSeq(t) == TreeSeq(A)+[x]+TreeSeq(B)+[y]+TreeSeq(C);
        var s' := BSTNode(A,x,BSTNode(B,y,C));
        assert TreeSeq(s') == TreeSeq(A)+[x]+TreeSeq(B)+[y]+TreeSeq(C);
        s := ZagZig(s');
        assert TreeSeq(s) == TreeSeq(s');
    }
    else // p[..2]==[1,1]
    {
        //     x
        //    / \
        //   /   \
        //  A     y
        //       / \
        //      B   C
        var x := RootValue(t);
        var A := Left(t);
        var y := RootValue(Right(t));
        var B := Left(Right(t));
        var C := SplayPath(Right(Right(t)),p[2..]);
        assert TreeSeq(C) == TreeSeq(Right(Right(t)));
        assert TreeSeq(t) == TreeSeq(A)+[x]+TreeSeq(B)+[y]+TreeSeq(C);
        var s' := BSTNode(A,x,BSTNode(B,y,C));
        assert TreeSeq(s') == TreeSeq(A)+[x]+TreeSeq(B)+[y]+TreeSeq(C);
        s := ZagZag(s');
        assert TreeSeq(s) == TreeSeq(s');
        assert SeqIsSorted(TreeSeq(s));
    }
    SortedSeqImpliesSortedTree(s);
}

method FindPath( t: BST, x: int ) returns( p: seq<dir>, r: BST )
    requires TreeIsSorted(t)
    ensures IsTreePath(t,p)
    ensures r == Subtree(t,p)
    ensures t != BSTEmpty ==> r != BSTEmpty
    ensures x in TreeSeq(t) ==> RootValue(r) == x
{
    match t 
    case BSTEmpty => { return [],t; }
    case BSTNode(A,z,B) =>
    {
        if z == x { return [],t; }
        if z > x
        {
            assert forall u | u in TreeSeq(B) :: u >= z;
            assert x in TreeSeq(t) ==> x in TreeSeq(A);
            p,r := FindPath(A,x);
            if r != BSTEmpty
            {
                p := [0]+p;
            }
            else
            {
                return [],t;
            }
        }
        else
        {
            p,r := FindPath(B,x);
            if r != BSTEmpty
            {
                p := [1]+p;
            }
            else
            {
                return [],t;
            }
        }
    }
}

method Splay( t: BST, x: int ) returns( s: BST )
    requires TreeIsSorted(t)
    ensures TreeSeq(s) == TreeSeq(t)
    ensures x in TreeSeq(t) ==> RootValue(s) == x
{
    var p,r := FindPath(t,x);
    if r == BSTEmpty { return t; }
    s := SplayPath(t,p);
}

method InsertPath( t: BST, x: int ) returns( s: BST, p: seq<dir> )
    requires TreeIsSorted(t)
    ensures TreeIsSorted(s)
    ensures multiset(TreeSeq(s)) == multiset(TreeSeq(t))+multiset{x}
    ensures IsTreePath(s,p)
    ensures Subtree(s,p) != BSTEmpty
    ensures RootValue(Subtree(s,p)) == x
{
    match t 
    case BSTEmpty => { return BSTNode(BSTEmpty,x,BSTEmpty),[]; }
    case BSTNode(A,z,B) =>
    {
        if x < z 
        {
            assert forall u | u in TreeSeq(B) :: u > x;
            assert multiset(TreeSeq(t)) == multiset(TreeSeq(A))+multiset{z}+multiset(TreeSeq(B));
            s,p := InsertPath(A,x);
            assert multiset(TreeSeq(s)) == multiset(TreeSeq(A))+multiset{x};
            assert RootValue(Subtree(s,p)) == x;
            assert TreeIsSorted(s);
            var s' := BSTNode(s,z,B);
            assert TreeSeq(s') == TreeSeq(s)+[z]+TreeSeq(B);
            assert TreeIsSorted(s) && TreeIsSorted(B);
            assert forall u | u in TreeSeq(s) :: u in multiset(TreeSeq(A))+multiset{x};
            assert forall u | u in TreeSeq(s) :: u in TreeSeq(A) || u == x;
            assert forall u | u in TreeSeq(s) :: u <= z;
            assert forall u | u in TreeSeq(B) :: u >= z;
            assert TreeIsSorted(s');
            p := [0]+p;
            s := s';
            return;
        }
        else
        {
            s,p := InsertPath(B,x);
            assert multiset(TreeSeq(s)) == multiset(TreeSeq(B))+multiset{x};
            assert RootValue(Subtree(s,p)) == x;
            assert TreeIsSorted(s);
            var s' := BSTNode(A,z,s);
            assert TreeSeq(s') == TreeSeq(A)+[z]+TreeSeq(s);
            assert TreeIsSorted(s) && TreeIsSorted(A);
            assert forall u | u in TreeSeq(s) :: u in multiset(TreeSeq(B))+multiset{x};
            assert forall u | u in TreeSeq(s) :: u in TreeSeq(B) || u == x;
            assert forall u | u in TreeSeq(s) :: u >= z;
            assert forall u | u in TreeSeq(A) :: u <= z;
            assert TreeIsSorted(s');
            p := [1]+p;
            s := s';
            return;
        }
    }
}

method InsertSplay( t: BST, x: int ) returns( s: BST )
    requires TreeIsSorted(t)
    ensures TreeIsSorted(s)
    ensures multiset(TreeSeq(s)) == multiset(TreeSeq(t))+multiset{x}
    ensures RootValue(s) == x
{
    var s',p := InsertPath(t,x);
    assert TreeIsSorted(s');
    s := SplayPath(s',p);
    assert TreeSeq(s') == TreeSeq(s);
    assert TreeIsSorted(s);
}

method DeleteSplay( t: BST, x: int ) returns( s: BST )
    requires TreeIsSorted(t)
    ensures TreeIsSorted(s)
    ensures multiset(TreeSeq(s)) == multiset(TreeSeq(t))-multiset{x}
{
    SortedTreeImpliesSortedSeq(t);
    if t == BSTEmpty { return t; }
    s := Splay(t,x);
    assert TreeSeq(s) == TreeSeq(t);
    SortedSeqImpliesSortedTree(s);
    assert TreeIsSorted(s);
    assert s != BSTEmpty;
    assert TreeSeq(s) == TreeSeq(t);
    assert x in TreeSeq(s) ==> RootValue(s) == x;
    if RootValue(s) != x
    {
        assert x !in TreeSeq(s);
        assert x !in multiset(TreeSeq(s));
        return;
    }
    var A := Left(s);
    var B := Right(s);
    if A == BSTEmpty { return B; }
    if B == BSTEmpty { return A; }
    assert TreeSeq(s) == TreeSeq(A)+[x]+TreeSeq(B);
    var A2 := SplayMax(A);
    assert Right(A2) == BSTEmpty;
    assert TreeSeq(A2) == TreeSeq(A);
    SortedTreeImpliesSortedSeq(A);
    SortedSeqImpliesSortedTree(A2);
    assert TreeIsSorted(A2);
    var A3 := Left(A2);
    var r := RootValue(A2);
    assert A2 == BSTNode(A3,r,BSTEmpty);
    assert TreeSeq(A2) == TreeSeq(BSTNode(A3,r,BSTEmpty)) == TreeSeq(A3)+[r]+TreeSeq(BSTEmpty);
    s := BSTNode(A3,r,B);
    assert TreeIsSorted(A3);
    assert TreeIsSorted(B);
    SortedTreeImpliesSortedSeq(A3);
    SortedTreeImpliesSortedSeq(B);
    assert TreeSeq(s) == TreeSeq(A3)+[r]+TreeSeq(B);
    assert forall u | u in TreeSeq(A3) :: u <= r;
    assert r in TreeSeq(A);
    assert r <= x;
    assert forall u | u in TreeSeq(B) :: r <= x <= u;
    ConcatSorted(TreeSeq(A3),[r],TreeSeq(A3)+[r]);
    ConcatSorted(TreeSeq(A3)+[r],TreeSeq(B),TreeSeq(A3)+[r]+TreeSeq(B));
    assert TreeSeq(s) == TreeSeq(A3)+[r]+TreeSeq(B);
    assert SeqIsSorted(TreeSeq(A3)+[r]+TreeSeq(B));
    assert SeqIsSorted(TreeSeq(s));
    SortedSeqImpliesSortedTree(s);
    assert TreeIsSorted(s);
}

lemma ConcatSorted( x: seq<int>, y: seq<int>, xy: seq<int> )
    requires xy == x+y
    requires forall p,q | 0 <= p < q < |x| :: x[p] <= x[q]
    requires forall p,q | 0 <= p < q < |y| :: y[p] <= y[q]
    requires forall z,w | z in x && w in y :: z <= w
    ensures forall p,q | 0 <= p < q < |xy| :: xy[p] <= xy[q]
{
    assert forall p,q | 0 <= p  < q < |xy| ::
        (0 <= p < q < |x|) ==> (xy[p] == x[p] <= x[q] == xy[q]);
    assert forall p,q | 0 <= p  < q < |xy| ::
        ((0 <= p < |x| && |x| <= q < |xy|) ==> xy[p] == x[p] && xy[p] in x && xy[q] in y);
    assert forall p,q | 0 <= p  < q < |xy| ::
        ((0 <= p < |x| && |x| <= q < |xy|) ==> xy[p] == x[p] && xy[p] in x && xy[q] in y && xy[p] <= xy[q]);
    assert forall p,q | 0 <= p  < q < |xy| ::
        ((0 <= p < q < |x|) && (xy[p] == x[p] <= x[q] == xy[q])) ||
        ((0 <= p < |x| && |x| <= q < |xy|) && xy[p] == x[p] && xy[p] in x && xy[q] in y && xy[p] <= xy[q]) ||
        ((|x| <= p < q < |xy|) && xy[p] == y[p-|x|] && xy[q] == y[q-|x|] && xy[p] <= xy[q]);
}