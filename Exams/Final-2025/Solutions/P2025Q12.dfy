lemma {:axiom} BisectionTermination( x: real, y: real, eps: real )
    requires eps > 0.0
    requires x >= eps > 0.0
    requires y == x/2.0
    ensures (x/eps).Floor > (y/eps).Floor

method Minimum( f: real->real
              , a: real
              , b: real
              , c: real
              , eps: real )
  returns( d: real, e: real )
    requires a < c
    requires b == (a+c)/2.0
    requires eps > 0.0
    requires f(b) <= f(a)
    requires f(b) <= f(c)
    ensures a <= d < e <= c
    ensures e-d < eps
    ensures f((d+e)/2.0) <= f(d)
    ensures f((d+e)/2.0) <= f(e)
{
    d, e := a, c;
    var m := b;
    while e-d >= eps
        decreases ((e-d)/eps).Floor
        invariant a <= d < e <= c 
        invariant m == (d+e)/2.0
        invariant f(m) <= f(d)
        invariant f(m) <= f(e)
    {
        var m1 := (d+m)/2.0;
        var m2 := (m+e)/2.0;
        BisectionTermination(e-d,m-d,eps);
        if f(m1) <= f(m)
        {
            e := m;
            m := m1;
        }
        else if f(m2) <= f(m)
        {
            d := m;
            m := m2;
        }
        else
        {
            d := m1;
            e := m2;
        }
    }
}