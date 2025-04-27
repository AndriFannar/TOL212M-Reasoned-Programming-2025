include "BST.dfy"

/*
// Eftirfarandi lausn teldist rétt á prófi
// þótt Dafny samþykki hana ekki.
// Neðar í skránni er sama lausn með
// rökstuðningi sem Dafny samþykkir.
method SumTree( t: BST ) returns( s: int )
    ensures s == SumSeq(TreeSeq(t));
{
    if t == BSTEmpty { return 0; }
    var left := SumTree(Left(t));
    var right := SumTree(Right(t));
    s := left+RootValue(t)+right;
}
*/

function SumSeq( s: seq<int> ): int
{ 
  if s == [] then 0 else s[0]+SumSeq(s[1..])
}

lemma SumSeqLemma( a: seq<int>, b: seq<int> )
    ensures SumSeq(a+b) == SumSeq(a)+SumSeq(b)
{
    if a == []
    {
        assert a+b == b;
        assert SumSeq(a+b) == SumSeq(a)+SumSeq(b);
        return;
    }
    assert a == a[..1]+a[1..];
    SumSeqLemma(a[1..],b);
    assert a+b == a[..1]+a[1..]+b;
    calc ==
    {
        SumSeq(a+b);
        (a+b)[0]+SumSeq((a+b)[1..]);
        assert (a+b)[0] == a[0];
        assert (a+b)[1..] == a[1..]+b;
        a[0]+SumSeq(a[1..]+b);
        SumSeq(a)+SumSeq(b);
    }
}

method SumTree( t: BST ) returns( s: int )
    ensures s == SumSeq(TreeSeq(t))
{
    if t == BSTEmpty { return 0; }
    var left := SumTree(Left(t));
    var right := SumTree(Right(t));
    assert TreeSeq(t) == TreeSeq(Left(t))+[RootValue(t)]+TreeSeq(Right(t));
    SumSeqLemma(TreeSeq(Left(t)),[RootValue(t)]);
    SumSeqLemma(TreeSeq(Left(t))+[RootValue(t)],TreeSeq(Right(t)));
    calc ==
    {
        SumSeq(TreeSeq(t));
        SumSeq(TreeSeq(Left(t))+[RootValue(t)]+TreeSeq(Right(t)));
        SumSeq(TreeSeq(Left(t)))+RootValue(t)+SumSeq(TreeSeq(Right(t)));
    }
    s := left+RootValue(t)+right;
}