// Recursive solution
method MinRecursive( x: seq<int> ) returns( m: int )
    requires |x| > 0
    ensures m in x
    ensures forall j | 0 <= j < |x| :: x[j] >= m
{
    if |x| == 1 { return x[0]; }
    m := MinRecursive(x[1..]);
    if x[0] < m { return x[0]; }
}

// Loop solution
method MinLoop( x: seq<int> ) returns( m: int )
    requires |x| > 0
    ensures m in x
    ensures forall j | 0 <= j < |x| :: x[j] >= m
{
    m := x[0];
    var i := 1;
    while i != |x|
        invariant m in x
        invariant 1 <= i <= |x|
        invariant forall j | 0 <= j < i :: x[j] >= m;
    {
        if x[i] < m { m := x[i]; }
        i := i+1;
    }
}