// Author: Snorri Agnarsson, snorri@hi.is

// Simplified samplesort

lemma ConcatSorted2( x: seq<int>, y: seq<int>, xy: seq<int> )
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

method MinOfMultiset( m: multiset<int> ) returns ( min: int )
    requires m != multiset{}
    ensures min in m
    ensures forall z | z in m :: min <= z
{
    min :| min in m;
    ghost var r := multiset{min};
    var s := m-multiset{min};
    while s != multiset{}
        decreases |s|
        invariant r+s == m
        invariant min in r
        invariant forall z | z in r :: min <= z
    {
        var tmp :| tmp in s;
        r := r+multiset{tmp};
        s := s-multiset{tmp};
        if tmp < min { min := tmp; }
    }
}

method SelectionSort( m: multiset<int> ) returns ( r: seq<int> )
    ensures multiset(r) == m
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
{
    r := [];
    var s := m;
    while s != multiset{}
        decreases |s|
        invariant m == s+multiset(r)
        invariant forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
        invariant forall v,w | v in r && w in s :: v <= w
    {
        var min := MinOfMultiset(s);
        s := s-multiset{min};
        ConcatSorted2(r,[min],r+[min]);
        r := r+[min];
    }
}

function UnionAll<T>( r: seq<multiset<T>> ): multiset<T>
    decreases |r|
{
    if r == [] then
        multiset{}
    else
        r[0]+UnionAll(r[1..])
}

lemma UnionAllLemma<T>( r: seq<multiset<T>> )
    ensures forall z | z in UnionAll(r) :: exists i | 0 <= i < |r| :: z in r[i]
{}

lemma UnionAllEmptyLemma<T>( r: seq<multiset<T>> )
    decreases |r|
    requires forall i | 0 <= i < |r| :: r[i] == multiset{}
    ensures UnionAll(r) == multiset{}
{
    if |r| == 0 { return; }
    UnionAllEmptyLemma(r[1..]);
}

lemma ConcatAllEmptyLemma<T>( r: seq<seq<T>> )
    decreases |r|
    requires forall i | 0 <= i < |r| :: r[i] == []
    ensures ConcatAll(r) == []
{
    if |r| == 0 { return; }
    ConcatAllEmptyLemma(r[1..]);
}

lemma UnionAllConcatLemma<T>( a: seq<multiset<T>>, b: seq<multiset<T>> )
    decreases |a|
    ensures UnionAll(a+b) == UnionAll(a)+UnionAll(b)
{
    if |a| == 0
    {
        assert a+b == b;
        return;
    }
    UnionAllConcatLemma(a[1..],b);
    assert (a+b)[..1] == a[..1];
    assert (a+b)[1..] == a[1..]+b;
    assert a+b == (a+b)[..1]+(a+b)[1..];
    calc ==
    {
        UnionAll(a+b);
        a[0]+UnionAll((a+b)[1..]);
        a[0]+UnionAll(a[1..]+b);
        a[0]+UnionAll(a[1..])+UnionAll(b);
        UnionAll(a)+UnionAll(b);
    }
}

lemma UnionAllAddingLemma<T>( r: seq<multiset<T>>, i: int, x: T )
    decreases i
    requires 0 <= i < |r|
    ensures UnionAll(r[i:=r[i]+multiset{x}]) == UnionAll(r)+multiset{x}
    ensures UnionAll(r[i:=r[i]+multiset{x}]) == multiset{x}+UnionAll(r)
{
    if i == 0 { return; }
    ghost var prefix := r[..i];
    ghost var suffix := r[i..];
    assert r == prefix+suffix;
    UnionAllConcatLemma(prefix,suffix);
    assert r[i:=r[i]+multiset{x}][i..] == suffix[0:=suffix[0]+multiset{x}];
    UnionAllAddingLemma(suffix,0,x);
    UnionAllConcatLemma(r[..i],suffix[0:=suffix[0]+multiset{x}]);
    assert r[i:=r[i]+multiset{x}] == r[..i]+r[i:=r[i]+multiset{x}][i..];
    assert r[i:=r[i]+multiset{x}] == r[..i]+suffix[0:=r[i]+multiset{x}];
    calc ==
    {
        UnionAll(r[i:=r[i]+multiset{x}]);
        UnionAll(r[..i])+UnionAll(suffix[0:=suffix[0]+multiset{x}]);
        UnionAll(r[..i])+UnionAll(suffix)+multiset{x};
        UnionAll(r[..i])+UnionAll(r[i..])+multiset{x};
        UnionAll(r)+multiset{x};
    }
}

function ConcatAll<T>( s: seq<seq<T>> ): seq<T>
    decreases |s|
{
    if s == [] then
        []
    else
        s[0]+ConcatAll(s[1..])
}

function Map<T,U>( f:T->U, x: seq<T> ): seq<U>
    decreases x
    requires forall z | z in x :: f.requires(z)
    ensures |Map(f,x)| == |x|
    ensures forall i | 0 <= i < |x| :: Map(f,x)[i] == f(x[i])
{
    if x == [] then
        []
    else
        [f(x[0])]+Map(f,x[1..])
}

lemma ConcatAllLemma<T>( a: seq<seq<T>>, b: seq<seq<T>> )
    decreases a
    ensures ConcatAll(a+b) == ConcatAll(a)+ConcatAll(b)
    ensures multiset(ConcatAll(a+b)) == multiset(ConcatAll(a))+multiset(ConcatAll(b))
    ensures multiset(ConcatAll(a)) == UnionAll(Map(z=>multiset(z),a))
    ensures UnionAll(Map(z=>multiset(z),a+b)) == UnionAll(Map(z=>multiset(z),a))+UnionAll(Map(z=>multiset(z),b))
{
    if a == []
    {
        assert a+b == b;
        return;
    }
    assert a+b == (a+b)[..1]+(a+b)[1..];
    assert (a+b)[..1] == a[..1];
    assert (a+b)[1..] == a[1..]+b;
    ConcatAllLemma(a[1..],b);
    calc ==
    {
        ConcatAll(a+b);
        (a+b)[0]+ConcatAll((a+b)[1..]);
        (a+b)[0]+ConcatAll(a[1..]+b);
    }
}

method SeqOfEquals( x: multiset<int>, z: int ) returns ( y: seq<int> )
    requires forall w | w in x :: w == z
    ensures multiset(y) == x
    ensures forall i,j | 0 <= i < j < |y| :: y[i] <= y[j]
    ensures forall i | 0 <= i < |y| :: y[i] == z
{
    y := [];
    var x' := x;
    while x' != multiset{}
        invariant x == x'+multiset(y)
        invariant forall i | 0 <= i < |y| :: y[i] == z
        decreases x'
    {
        var tmp :| tmp in x';
        x' := x'-multiset{tmp};
        y := [tmp]+y;
    }
}

method Sample1<T>( x: multiset<T>, s: multiset<T> ) returns ( x': multiset<T>, s': multiset<T> )
    requires |x| >= 1
    ensures exists r | r in x :: x == x'+multiset{r} && s' == s+multiset{r}
    ensures |x'| == |x|-1
    ensures |s'| == |s|+1
{
    var r :| r in x;
    x' := x-multiset{r};
    s' := s+multiset{r};
}

method Samplesort255Partition( x: multiset<int>, p: seq<int> )
        returns( r: seq<multiset<int>> )
    requires |p| == 255
    requires forall i,j | 0 <= i < j < 15 :: p[i] <= p[j]
    ensures |r| == 256
    ensures UnionAll(r) == x
    ensures forall q | 0 <= q < 255 && q%2 == 0 :: forall z | z in r[q] :: z < p[q]
    ensures forall q | 0 <= q < 255 && q%2 == 1 :: forall z | z in r[q] :: z <= p[q]
    ensures forall q | 1 <= q < 256 && q%2 == 0 :: forall z | z in r[q] :: p[q-1] < z
    ensures forall q | 1 <= q < 256 && q%2 == 1 :: forall z | z in r[q] :: p[q-1] <= z
{
    var r' := new multiset<int>[256](_=>multiset{});
    UnionAllEmptyLemma(r'[..]);
    var x' := x;
    while x' != multiset{}
        decreases x'
        invariant UnionAll(r'[..])+x' == x
        invariant r'.Length == 256
        invariant forall q | 0 <= q < 255 && q%2 == 0 :: forall z | z in r'[q] :: z < p[q]
        invariant forall q | 0 <= q < 255 && q%2 == 1 :: forall z | z in r'[q] :: z <= p[q]
        invariant forall q | 1 <= q < 256 && q%2 == 0 :: forall z | z in r'[q] :: p[q-1] < z
        invariant forall q | 1 <= q < 256 && q%2 == 1 :: forall z | z in r'[q] :: p[q-1] <= z
    {
        var z :| z in x';
        x' := x'-multiset{z};
        var add := multiset{z};
        var i := 0;
        assert i%2 == 0;
        if p[127] < z  { i := i+128; assert i%2 == 0; }
        if p[i+63] < z { i := i+64;  assert i%2 == 0; }
        if p[i+31] < z { i := i+32;  assert i%2 == 0; }
        if p[i+15] < z { i := i+16;  assert i%2 == 0; }
        if p[i+7] < z  { i := i+8;   assert i%2 == 0; }
        if p[i+3] < z  { i := i+4;   assert i%2 == 0; }
        if p[i+1] < z  { i := i+2;   assert i%2 == 0; }
        assert i%2 == 0;
        if p[i] <= z   { i := i+1;   assert i%2 == 1; }
        UnionAllAddingLemma(r'[..],i,z);
        r'[i] := r'[i]+add;
    }
    r := r'[..];
}

lemma SampleSortLemma( r: seq<multiset<int>>, s: seq<seq<int>> )
    decreases r
    requires Map(z=>multiset(z),s) == r
    requires forall p,q | 0 <= p < q < |r| :: forall z,w | z in r[p] && w in r[q] :: z <= w
    requires forall z | z in s :: forall p,q | 0 <= p < q < |z| :: z[p] <= z[q]
    ensures multiset(ConcatAll(s)) == UnionAll(r)
    ensures forall p,q | 0 <= p < q < |ConcatAll(s)| :: ConcatAll(s)[p] <= ConcatAll(s)[q]
{
    if r == [] { return; }
    SampleSortLemma(r[1..],s[1..]);
    assert ConcatAll(s) == s[0]+ConcatAll(s[1..]);
    assert forall p | 0 <= p < |s[0]| :: ConcatAll(s)[p] == s[0][p];
    assert forall p | 0 <= p < |s[0]| :: ConcatAll(s)[p] in r[0];
    assert forall p | |s[0]| <= p < |ConcatAll(s)| :: ConcatAll(s)[p] == ConcatAll(s[1..])[p-|s[0]|];
    assert forall p | |s[0]| <= p < |ConcatAll(s)| :: ConcatAll(s)[p] in UnionAll(r[1..]);
    UnionAllLemma(r[1..]);
    assert forall w | w in UnionAll(r[1..]) :: exists p | 1 <= p < |r| :: w in r[p];
    assert forall z,w | z in r[0] && w in UnionAll(r[1..]) :: z <= w;
    assert forall p,q | 0 <= p < |s[0]| && |s[0]| <= q < |ConcatAll(s)| :: ConcatAll(s)[p] <= ConcatAll(s)[q];
    assert forall p,q | 0 <= p < q < |ConcatAll(s)| :: ConcatAll(s)[p] <= ConcatAll(s)[q];
}

method Samplesort255( x: multiset<int>, d: int ) returns ( y: seq<int> )
    decreases d
    requires d >= 0
    ensures multiset(y) == x
    ensures forall i,j | 0 <= i < j < |y| :: y[i] <= y[j]
{
    var nx := |x|;
    if d == 0 || nx < 255
    {
        y := SelectionSort(x);
        return;
    }
    var p := AscendingSample(x,255);
    var r := Samplesort255Partition(x,p);
    var s: seq<seq<int>> := [];
    var i := 0;
    while i != 256
        decreases 256-i
        invariant |s| == i
        invariant 0 <= i <= 256
        invariant UnionAll(r) == x
        invariant Map(z=>multiset(z),s) == r[..i]
        invariant forall i,j | 0 <= i < j < 255 :: p[i] <= p[j]
        invariant forall i | 0 < i < 255 :: forall z | z in r[i] :: p[i-1] <= z <= p[i]
        invariant forall z | z in s :: forall p,q | 0 <= p < q < |z| :: z[p] <= z[q]
        invariant forall p,q | 0 <= p < q < 256 :: forall z,w | z in r[p] && w in r[q] :: z <= w
    {
        var tmp: seq<int>;
        if 0 < i < 255 && p[i-1] == p[i] { tmp := SeqOfEquals(r[i],p[i]);  }
        else                             { tmp := Samplesort255(r[i],d-1); }
        s := s+[tmp];
        i := i+1;
    }
    y := ConcatAll(s);
    SampleSortLemma(r,s);
}

method AscendingSample( x: multiset<int>, n: int ) returns( p: seq<int> )
    requires n >= 0
    requires |x| >= n
    ensures |p| == n
    ensures forall i,j | 0 <= i < j < n :: p[i] <= p[j]
    ensures multiset(p) <= x
{
    var s: multiset<int> := multiset{};
    var x' := x;
    var i := 0;
    while i != n
        decreases n-i
        invariant s+x' == x
        invariant |s| == i
        invariant |x'| >= n-i
        invariant 0 <= i <= n
    {
        x', s := Sample1(x',s);
        i := i+1;
    }
    p := SelectionSort(s);
}

class Random
{
    var x: int

    predicate Valid()
        reads this
    {
        0 <= x < 4294967296
    }

    constructor()
        ensures Valid()
    {
        x := 1234567890;
    }

    method Next() returns ( r: int )
        modifies this
        requires Valid()
        ensures Valid()
        ensures 0 <= r < 4294967296
    {
        r := x;
        x := (x*1664525+1013904223)%4294967296;
    }
}

method Test()
{
    var count := 1000;
    var r := new Random();
    var a := new int[count](_=>0);
    var i := 0;
    print "Generating...";
    while i != count
        decreases count-i
        invariant r.Valid()
        invariant 0 <= i <= count
    {
        var x := r.Next();
        a[i] := x%count;
        i := i+1;
    }
    print "Sorting...";
    var s := Samplesort255(multiset(a[..]),10);
    print "Done\n";
}

method Main() { Test(); }