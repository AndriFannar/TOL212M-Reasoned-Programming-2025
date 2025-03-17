// Höfundur: Snorri Agnarsson, snorri@hi.is

method Samplesort7Partition( x: multiset<int>, p: seq<int> )
        returns( r: seq<multiset<int>> )
    requires |p| == 7
    requires forall i,j | 0 <= i < j < 7 :: p[i] <= p[j]
    ensures |r| == 8
    ensures r[0]+r[1]+r[2]+r[3]+r[4]+r[5]+r[6]+r[7] == x
    ensures forall z | z in r[0] :: z < p[0]
    ensures forall z | z in r[1] :: p[0] <= z <= p[1]
    ensures forall z | z in r[2] :: p[1] < z < p[2]
    ensures forall z | z in r[3] :: p[2] <= z <= p[3]
    ensures forall z | z in r[4] :: p[3] < z < p[4]
    ensures forall z | z in r[5] :: p[4] <= z <= p[5]
    ensures forall z | z in r[6] :: p[5] < z < p[6]
    ensures forall z | z in r[7] :: p[6] <= z
{
    var r' := new multiset<int>[8](_ => multiset{});
    var x' := x;
    while x' != multiset{}
        decreases x'
        invariant r'[0]+r'[1]+r'[2]+r'[3]+r'[4]+r'[5]+r'[6]+r'[7]+x' == x
        invariant forall z | z in r'[0] :: z < p[0]
        invariant forall z | z in r'[1] :: p[0] <= z <= p[1]
        invariant forall z | z in r'[2] :: p[1] < z < p[2]
        invariant forall z | z in r'[3] :: p[2] <= z <= p[3]
        invariant forall z | z in r'[4] :: p[3] < z < p[4]
        invariant forall z | z in r'[5] :: p[4] <= z <= p[5]
        invariant forall z | z in r'[6] :: p[5] < z < p[6]
        invariant forall z | z in r'[7] :: p[6] <= z
    {
        var z :| z in x';
        x' := x'-multiset{z};
        var i := 0;
        if p[3] < z   { i := i+4; }
        if p[i+1] < z { i := i+2; }
        if p[i] <= z  { i := i+1; }
        r'[i] := r'[i]+multiset{z};
    }
    r := r'[..];
}

method Samplesort7( x: multiset<int> ) returns ( y: seq<int> )
    ensures multiset(y) == x
    decreases |x|
    ensures forall i,j | 0 <= i < j < |y| :: y[i] <= y[j]
{
    if |x| < 7
    {
        y := SelectionSort(x);
        return;
    }
    var p := AscendingSample(x,7);
    var r := Samplesort7Partition(x,p);
    var s0 := SelectionSort(r[0]);
    var s1: seq<int>;
    if p[0] == p[1] { s1 := SeqOfEquals(r[1],p[0]); }
    else            { s1 := SelectionSort(r[1]);    }
    var s2 := SelectionSort(r[2]);
    var s3: seq<int>;
    if p[2] == p[3] { s3 := SeqOfEquals(r[3],p[2]); }
    else            { s3 := SelectionSort(r[3]);    }
    var s4 := SelectionSort(r[4]);
    var s5: seq<int>;
    if p[4] == p[5] { s5 := SeqOfEquals(r[5],p[4]); }
    else            { s5 := SelectionSort(r[5]);    }
    var s6 := SelectionSort(r[6]);
    var s7 := SelectionSort(r[7]);
    y := s0+s1+s2+s3+s4+s5+s6+s7;
    assert forall j | 0 <= j < |s0| :: y[j] in r[0];
    assert forall j | |s0| <= j < |s0+s1| :: y[j] in r[1];
    assert forall j | |s0+s1| <= j < |s0+s1+s2| :: y[j] in r[2];
    assert forall j | |s0+s1+s2| <= j < |s0+s1+s2+s3| :: y[j] in r[3];
    assert forall j | |s0+s1+s2+s3| <= j < |s0+s1+s2+s3+s4| :: y[j] in r[4];
    assert forall j | |s0+s1+s2+s3+s4| <= j < |s0+s1+s2+s3+s4+s5| :: y[j] in r[5];
    assert forall j | |s0+s1+s2+s3+s4+s5| <= j < |s0+s1+s2+s3+s4+s5+s6| :: y[j] in r[6];
    assert forall j | |s0+s1+s2+s3+s4+s5+s6| <= j < |y| :: y[j] in r[7];
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
        invariant 0 <= i <= n
    {
        x', s := Sample1(x',s);
        i := i+1;
    }
    p := SelectionSort(s);
}

method Test()
{
    var m := multiset{5,1,4,2,3,4,3,2,1,1,2,3,4,5,1,2,3,4,5,1,2,3,4,5};
    {
        var s := Samplesort7(m);
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

method Main() { Test(); }

//////////////////////////////////////////////////////////////
// Hér fyrir aftan eru hjálparföll og hjálparsetningar
//////////////////////////////////////////////////////////////

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

method Sample1( x: multiset<int>, s: multiset<int> ) returns ( x': multiset<int>, s': multiset<int> )
    requires |x| >= 1
    ensures exists r | r in x :: x == x'+multiset{r} && s' == s+multiset{r}
    ensures |x'| == |x|-1
    ensures |s'| == |s|+1
{
    var r :| r in x;
    x' := x-multiset{r};
    s' := s+multiset{r};
}