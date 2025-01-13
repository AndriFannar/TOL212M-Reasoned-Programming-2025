function Max( x: int, y: int ): int
    ensures Max(x,y) == x || Max(x,y) == y
    ensures Max(x,y) >= x && Max(x,y) >= y
{
    if x > y then
        x
    else
        y
}

function MaxSeq( a: seq<int> ): int
    requires a != []
    ensures MaxSeq(a) in a 
    ensures a == [a[0]]+a[1..]
    ensures forall u | u in a :: u <= MaxSeq(a)
{
    if |a|==1 then a[0] else Max(a[0],MaxSeq(a[1..]))
}

method MaxRecursive( a: seq<int> ) returns( m: int )
    requires a != []
    ensures m in a 
    ensures forall u | u in a :: m >= u
{
    if |a| == 1 { return a[0]; }
    m := MaxRecursive(a[1..]);
    assert a == a[..1]+a[1..];
    m := Max(a[0],m);
}

function SumSeq( a: seq<int> ): int
{
    if a == [] then
        0
    else
        SumSeq(a[..|a|-1])+a[|a|-1]
}

method SumRecursive( a: seq<int> ) returns( s: int )
    ensures s == SumSeq(a)
{
    if a == [] { return 0; }
    s := SumRecursive(a[..|a|-1]);
    s := s+a[|a|-1];
}

method SumLoop( a: seq<int> ) returns( s: int )
    ensures s == SumSeq(a)
{
    s := 0;
    var i := 0;
    while i != |a|
        invariant 0 <= i <= |a|
        invariant s == SumSeq(a[..i])
    {
        s := s+a[i];
        i := i+1;
        assert a[..i] == a[..i-1]+a[i-1..i];
    }
    assert a == a[..i];
}

method ArraySum( a: array<int> ) returns( s: int )
    ensures s == SumSeq(a[..])
{
    s := 0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant s == SumSeq(a[..i])
    {
        s := s+a[i];
        i := i+1;
        assert a[..i] == a[..i-1]+a[i-1..i];
    }
    assert a[..] == a[..i];
}

method PartialSums( a: array<int> )
    modifies a
    ensures forall i | 0 <= i < a.Length :: a[i] == SumSeq(old(a[..i+1]))
{
    var i := 0;
    var s := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant a[i..] == old(a[i..])
        invariant s == SumSeq(old(a[..i]))
        invariant forall k | 0 <= k < i :: a[k] == SumSeq(old(a[..k+1]))
    {
        s := s+a[i];
        assert old(a[..i+1]) == old(a[..i]+[a[i]]);
        a[i] := s;
        i := i+1;
    }
}

method Mul( x: int, y: int ) returns( p: int )
    decreases y
    requires y >= 0
    ensures p == x*y
{
    if y == 0 { return 0; }
    if y%2 == 1
    {
        p := Mul(x+x,y/2);
        p := x+p;
    }
    else
    {
        assert y%2 == 0;
        p := Mul(x+x,y/2);
    }
}