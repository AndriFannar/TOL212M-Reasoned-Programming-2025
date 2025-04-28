/*
Program the body of the function below. Use recursion and not a loop.

method Root( f: real->real, a: real, b: real, eps: real )
  returns( c: real, d: real )
    decreases ((b-a)/eps).Floor;
    requires a < b;
    requires eps > 0.0;
    requires f(a)*f(b) <= 0.0;
    ensures a <= c < d <= b;
    ensures d-c < eps;
    ensures f(c)*f(d) <= 0.0;

Hint: the following lemma can be proven in Dafny. You do not need to call it. 

lemma BisectionTermination( a: real, b: real, eps: real )
    requires b-a >= eps > 0.0;
    ensures ((b-a)/eps).Floor > ((b-a)/2.0/eps).Floor;
*/

lemma {:axiom} BisectionTermination( a: real, b: real, eps: real )
    requires b-a >= eps > 0.0
    ensures ((b-a)/eps).Floor > ((b-a)/2.0/eps).Floor

method Root( f: real->real, a: real, b: real, eps: real ) returns( c: real, d: real )
    decreases ((b-a)/eps).Floor
    requires a < b
    requires eps > 0.0
    requires f(a)*f(b) <= 0.0
    ensures a <= c < d <= b
    ensures d-c < eps
    ensures f(c)*f(d) <= 0.0
{
    if b-a < eps { return a, b; }
    BisectionTermination(a,b,eps); // This is not necessary in an exam
    var m := (a+b)/2.0;

    // The following assert is not necessary in an exam
    assert f(a)*f(m) > 0.0 ==> f(m)/f(a) > 0.0 && f(m)*f(b) == f(a)*f(b)*(f(m)/f(a)) <= 0.0;

    if f(a)*f(m) <= 0.0 { c,d := Root(f,a,m,eps); }
    else                { c,d := Root(f,m,b,eps); }
}