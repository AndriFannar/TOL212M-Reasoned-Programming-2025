// Author: Snorri Agnarsson.

method DijkstraPartition( x: multiset<int> )
        returns ( a: multiset<int>, b: multiset<int>, c: multiset<int> )
    requires x != multiset{}
    ensures a+b+c == x
    ensures |b| > 0
    ensures forall p,q | p in b && q in b :: p == q
    ensures forall p,q | p in a && q in b :: p < q
    ensures forall p,q | p in b && q in c :: p < q
{
    var y := x;
    var z: multiset<int> := multiset{};
    var pivot :| pivot in x;
    y := y-multiset{pivot};
    a := multiset{};
    b := multiset{pivot};
    c := multiset{};
    while y != multiset{}
        decreases y
        invariant |b| > 0
        invariant a+b+c+y == x
        invariant forall z | z in b :: z == pivot
        invariant forall z | z in a :: z < pivot
        invariant forall z | z in c :: z > pivot
    {
        var tmp :| tmp in y;
        y := y-multiset{tmp};
        if tmp < pivot      { a := a+multiset{tmp}; }
        else if tmp > pivot { c := c+multiset{tmp}; }
        else                { b := b+multiset{tmp}; }
    }
}

method DijkstraQuickselect( x: multiset<int>, k: int )
        returns( a: multiset<int>, b: multiset<int>, c: multiset<int> )
    requires 0 <= k < |x|
    decreases x
    ensures a+b+c == x
    ensures forall p,q | p in b && q in b :: p == q
    ensures forall p,q | p in a && q in b :: p < q
    ensures forall p,q | p in b && q in c :: p < q
    ensures forall p,q | p in a && q in c :: p < q
    ensures |a| <= k < |a|+|b|
{
    if |x| == 1
    {
        a := multiset{};
        b := x;
        c := multiset{};
        ghost var bx :| bx in b;
        assert |x-multiset{bx}| == 0;
        assert x == multiset{bx};
        return;
    }
    a, b, c := DijkstraPartition(x);
    if k < |a|
    {
        var a', b', c' := DijkstraQuickselect(a,k);
        assert forall q | q in b' :: q in a;
        a, b, c := a', b', c'+b+c;
    }
    else if k >= |a|+|b|
    {
        var a',b',c' := DijkstraQuickselect(c,k-|a|-|b|);
        assert forall q | q in b' :: q in c;
        a, b, c := a+b+a', b', c';
    }
}

method SeqOfMultiset( x: multiset<int> ) returns ( y: seq<int> )
    ensures multiset(y) == x
{
    y := [];
    var x' := x;
    while x' != multiset{}
        invariant x == x'+multiset(y)
        decreases x'
    {
        var tmp :| tmp in x';
        x' := x'-multiset{tmp};
        y := [tmp]+y;
    }
}

method DijkstraQuicksort( x: multiset<int> ) returns( y: seq<int> )
    decreases x
    ensures multiset(y) == x
    ensures forall p,q | 0 <= p < q < |y| :: y[p] <= y[q]
{
    if x == multiset{} { return []; }
    var a, b, c := DijkstraPartition(x);
    var a' := DijkstraQuicksort(a);
    var b' := SeqOfMultiset(b);
    var c' := DijkstraQuicksort(c);
    y := a'+b'+c';
    assert forall i | 0 <= i < |a'| :: y[i] in a;
    assert forall i | |a'| <= i < |a'+b'| :: y[i] in b;
    assert forall i | |a'+b'| <= i < |y| :: y[i] in c;
}

method LomutoPartition( x: multiset<int> )
        returns ( a: multiset<int>, p: int, b: multiset<int> )
    requires x != multiset{}
    ensures x == multiset{p}+a+b
    ensures forall z | z in a :: z <= p
    ensures forall z | z in b :: z >= p
{
    p :| p in x;
    var x' := x-multiset{p};
    a := multiset{};
    b := multiset{};
    while x' != multiset{}
        decreases x'
        invariant multiset{p}+a+b+x' == x
        invariant forall z | z in a :: z <= p
        invariant forall z | z in b :: z >= p
    {
        var tmp :| tmp in x';
        x' := x'-multiset{tmp};
        if tmp < p { a := a+multiset{tmp}; }
        else       { b := b+multiset{tmp}; }
    }
}

method LomutoQuicksort( x: multiset<int> ) returns ( y: seq<int> )
    decreases x
    ensures multiset(y) == x
    ensures forall p,q | 0 <= p < q < |y| :: y[p] <= y[q]
{
    if x == multiset{} { return []; }
    var a, pivot, b := LomutoPartition(x);
    var a' := LomutoQuicksort(a);
    var b' := LomutoQuicksort(b);
    y := a'+[pivot]+b';
    assert forall i | 0 <= i < |a'| :: y[i] in a;
    assert forall i | |a'|+1 <= i < |y| :: y[i] in b;
}

method LomutoQuickselect( x: multiset<int>, k: int )
        returns( a: multiset<int>, b: int, c: multiset<int> )
    requires 0 <= k < |x|
    decreases x
    ensures a+multiset{b}+c == x
    ensures forall p | p in a :: p <= b
    ensures forall p | p in c :: p >= b
    ensures |a| == k
{
    if |x| == 1
    {
        a := multiset{};
        b :| b in x;
        c := multiset{};
        assert |x-multiset{b}| == 0;
        return;
    }
    a, b, c := LomutoPartition(x);
    if k < |a|
    {
        var a', b', c' := LomutoQuickselect(a,k);
        assert b' in a;
        a, b, c := a', b', c'+multiset{b}+c;
    }
    else if k > |a|
    {
        var a',b',c' := LomutoQuickselect(c,k-|a|-1);
        assert b' in c;
        a, b, c := a+multiset{b}+a', b', c';
    }
}

method DualPivotPartition( x: multiset<int> )
        returns( a: multiset<int>, p: int, b: multiset<int>, q: int, c: multiset<int> )
    requires |x| >= 2
    ensures p <= q
    ensures x == a+b+c+multiset{p,q}
    ensures forall z | z in a :: z < p
    ensures forall z | z in c :: z > q
    ensures forall z | z in b :: p <= z <= q
{
    p :| p in x;
    var x' := x-multiset{p};
    assert x == x'+multiset{p};
    assert |x'| >= 1;
    q :| q in x';
    x' := x'-multiset{q};
    assert x == x'+multiset{p,q};
    if p > q { p,q := q,p; }
    a := multiset{};
    b := multiset{};
    c := multiset{};
    while x' != multiset{}
        decreases x'
        invariant x == a+b+c+multiset{p,q}+x'
        invariant forall z | z in a :: z < p
        invariant forall z | z in c :: z > q
        invariant forall z | z in b :: p <= z <= q
    {
        var tmp :| tmp in x';
        x' := x'-multiset{tmp};
        if tmp < p      { a := a+multiset{tmp}; }
        else if tmp > q { c := c+multiset{tmp}; }
        else            { b := b+multiset{tmp}; }
    }
}

method DualPivotQuicksort( x: multiset<int> ) returns( y: seq<int> )
    decreases x
    ensures multiset(y) == x
    ensures forall p,q | 0 <= p < q < |y| :: y[p] <= y[q]
{
    if |x| <= 1 { y := SeqOfMultiset(x); return; }
    var a, r, b, s, c := DualPivotPartition(x);
    var a' := DualPivotQuicksort(a);
    var b': seq<int>;
    if r < s { b' := DualPivotQuicksort(b); }
    else     { b' := SeqOfMultiset(b);      }
    var c' := DualPivotQuicksort(c);
    y := a'+[r]+b'+[s]+c';
    assert forall i | 0 <= i < |a'| :: y[i] in a;
    assert forall i | |a'| < i < |a'+[r]+b'| :: y[i] in b;
    assert forall i | |a'+[r]+b'| < i < |y| :: y[i] in c;
}

method TriplePivotPartition( x: multiset<int> )
        returns( a: multiset<int>, p: int, b: multiset<int>, q: int, c: multiset<int>, r: int, d: multiset<int> )
    requires |x| >= 3
    ensures p <= q <= r
    ensures x == a+b+c+d+multiset{p,q,r}
    ensures forall z | z in a :: z < p
    ensures forall z | z in b :: p <= z <= q
    ensures forall z | z in c :: q < z < r
    ensures forall z | z in d :: r <= z
{
    a := multiset{};
    b := multiset{};
    c := multiset{};
    d := multiset{};
    p :| p in x;
    var x' := x-multiset{p};
    assert x == x'+multiset{p};
    assert |x'| >= 2;
    assert x == a+b+c+d+x'+multiset{p};
    q :| q in x';
    x' := x'-multiset{q};
    assert |x'| >= 1;
    assert x == a+b+c+d+x'+multiset{p,q};
    assert x == x'+multiset{p,q};
    r :| r in x';
    x' := x'-multiset{r};
    assert x == a+b+c+d+x'+multiset{p,q,r};
    if p > q { p,q := q,p; }
    if q > r { q,r := r,q; }
    if p > q { p,q := q,p; }
    while x' != multiset{}
        decreases x'
        invariant x == a+b+c+d+x'+multiset{p,q,r}
        invariant forall z | z in a :: z < p
        invariant forall z | z in b :: p <= z <= q
        invariant forall z | z in c :: q < z < r
        invariant forall z | z in d :: r <= z
    {
        var tmp :| tmp in x';
        x' := x'-multiset{tmp};
        if tmp <= q 
        {
            if tmp < p { a := a+multiset{tmp}; }
            else       { b := b+multiset{tmp}; }
        }
        else
        {
            if tmp < r { c := c+multiset{tmp}; }
            else       { d := d+multiset{tmp}; }
        }
    }
}

method TriplePivotQuicksort( x: multiset<int> ) returns ( y: seq<int> )
    decreases x
    ensures multiset(y) == x
    ensures forall p,q | 0 <= p < q < |y| :: y[p] <= y[q]
{
    if |x| == 0 { return []; }
    if |x| == 1 { y := SeqOfMultiset(x); return; }
    if |x| == 2
    {
        var r :| r in x;
        var x' := x-multiset{r};
        assert |x'| == 1;
        assert x'+multiset{r} == x;
        var s :| s in x';
        x' := x'-multiset{s};
        assert |x'| == 0;
        assert x == multiset{r,s};
        if r > s { r, s := s, r; }
        return [r,s];
    }
    var a,p,b,q,c,r,d := TriplePivotPartition(x);
    var a' := TriplePivotQuicksort(a);
    var b': seq<int>;
    if p < q { b' := TriplePivotQuicksort(b); }
    else     { b' := SeqOfMultiset(b);        }
    var c' := TriplePivotQuicksort(c);
    var d' := TriplePivotQuicksort(d);
    y := a'+[p]+b'+[q]+c'+[r]+d';
    assert forall i | 0 <= i < |a'| :: y[i] in a;
    assert y[|a'|] == p;
    assert forall i | |a'| < i < |a'+[p]+b'| :: y[i] in b;
    assert y[|a'+[p]+b'|] == q;
    assert forall i | |a'+[p]+b'| < i < |a'+[p]+b'+[q]+c'| :: y[i] in c;
    assert y[|a'+[p]+b'+[q]+c'|] == r;
    assert forall i | |a'+[p]+b'+[q]+c'| < i < |y| :: y[i] in d;
    assert forall p,q | 0 <= p < q < |y| :: y[p] <= y[q];
}

method Main()
{
    var m := multiset{5,1,4,2,3,4,3,2,1,1,2,3,4,5,1,2,3,4,5,1,2,3,4,5};
    {
        var a,b,c := LomutoQuickselect(m,7);
        print b;
        print "\n";
    }
    {
        var a,b,c := DijkstraQuickselect(m,7);
        var s := SeqOfMultiset(b);
        var i := 0;
        while i != |s|
            decreases |s|-i
            invariant 0 <= i <= |s|
        {
            print s[i];
            print " ";
            i := i+1;
        }
        print "\n";
    }
    {
        var s := SeqOfMultiset(m);
        var i := 0;
        while i != |s|
            decreases |s|-i
            invariant 0 <= i <= |s|
        {
            print s[i];
            print " ";
            i := i+1;
        }
        print "\n";
    }
    {
        var s := DijkstraQuicksort(m);
        var i := 0;
        while i != |s|
            decreases |s|-i
            invariant 0 <= i <= |s|
        {
            print s[i];
            print " ";
            i := i+1;
        }
        print "\n";
    }
}