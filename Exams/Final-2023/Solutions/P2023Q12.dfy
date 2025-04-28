/*
Program the body of the function below. Use a loop and not recursion. Remember to put a decreases clause
in the loop. Consider the hint in the previous question.

method Root( f: real->real, a: real, b: real, eps: real )
  returns( c: real, d: real )
    requires a < b;
    requires eps > 0.0;
    requires f(a)*f(b) <= 0.0;
    ensures a <= c < d <= b;
    ensures d-c < eps;
    ensures f(c)*f(d) <= 0.0;
*/

lemma {:axiom} BisectionTermination( a: real, b: real, eps: real )
    requires b-a >= eps > 0.0
    ensures ((b-a)/eps).Floor > ((b-a)/2.0/eps).Floor

method Root( f: real->real, a: real, b: real, eps: real ) returns( c: real, d: real )
    requires a < b
    requires eps > 0.0
    requires f(a)*f(b) <= 0.0
    ensures a <= c < d <= b
    ensures d-c < eps
    ensures f(c)*f(d) <= 0.0
{
    c, d := a, b;
    while d-c >= eps
        invariant a <= c < d <= b
        decreases ((d-c)/eps).Floor
        invariant f(c)*f(d) <= 0.0
    {
        var m := (c+d)/2.0;

        // The following two lines are not necessary in an exam, but Dafny needs them
        assert f(c)*f(m) > 0.0 ==> f(m)/f(c) > 0.0 && f(m)*f(d) == f(c)*f(d)*(f(m)/f(c)) <= 0.0;
        BisectionTermination(c,d,eps);

        if f(c)*f(m) <= 0.0 { d := m; }
        else                { c := m; }
    }
}