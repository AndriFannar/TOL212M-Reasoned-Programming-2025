// Author: Snorri Agnarsson, snorri@hi.is

// Define raising to a power
function IntPow( x: int, y: int ): int
    decreases y
    requires y >= 0
    requires x >= 0
    ensures IntPow(x,y) >= 0
{
    if y == 0 then
        1
    else
        x*IntPow(x,y-1)
}

// Raising to a power efficiently
function IntPowEfficient( x: int, y: int ): int
    decreases y
    requires x >= 0
    requires y >= 0
    ensures IntPowEfficient(x,y) >= 0
    ensures x > 0 ==> IntPowEfficient(x,y) > 0
{
    if y == 0 then
        1
    else if y%2 == 0 then
        Square(IntPowEfficient(x,y/2))
    else
        x*Square(IntPowEfficient(x,y/2))
}

// Raising to a power efficiently
function IntPowEfficient2( x: int, y: int ): int
    decreases y
    requires x >= 0
    requires y >= 0
    ensures IntPowEfficient2(x,y) >= 0
    ensures x > 0 ==> IntPowEfficient2(x,y) > 0
{
    if y == 0 then
        1
    else if y%2 == 0 then
        IntPowEfficient2(Square(x),y/2)
    else
        x*IntPowEfficient2(Square(x),y/2)
}

// Define squaring
function Square( x: int ): int
{
    x*x
}

// x^(a+b) == (x^a)*(x^b)
lemma IntPowMulLemma( x: int, a: int, b: int )
    decreases a
    requires x >= 0 && a >= 0 && b >= 0
    ensures IntPow(x,a+b) == IntPow(x,a)*IntPow(x,b)
{
    if a == 0 { return; }
    IntPowMulLemma(x,a-1,b);
    assert IntPow(x,a+b) == x*IntPow(x,a+b-1);
}

lemma IntPowEfficientLemma( x: int, y: int )
    decreases y
    requires x >= 0
    requires y >= 0
    ensures IntPowEfficient(x,y) == IntPow(x,y)
    ensures IntPowEfficient2(x,y) == IntPow(x,y)
    ensures x > 0 ==> IntPow(x,y) > 0
{
    if y == 0 { return; }
    if y%2 == 0
    {
        IntPowEfficientLemma(x,y/2);
        IntPowMulLemma(x,y/2,y/2);
        calc ==
        {
            IntPowEfficient(x,y);
            Square(IntPowEfficient(x,y/2));
            IntPowEfficient(x,y/2)*IntPowEfficient(x,y/2);
            IntPow(x,y/2)*IntPow(x,y/2);
            IntPow(x,y);
        }
        return;
    }
    assert y/2+y/2 == y-1;
    IntPowEfficientLemma(x,y/2);
    IntPowMulLemma(x,y/2,y/2);
    IntPowEfficientLemma(x,y-1);
    IntPowMulLemma(x,y-1,1);
    calc ==
    {
        IntPowEfficient(x,y);
        x*Square(IntPowEfficient(x,y/2));
        x*(IntPowEfficient(x,y/2)*IntPowEfficient(x,y/2));
        assert IntPowEfficient(x,y/2)*IntPowEfficient(x,y/2) == IntPowEfficient(x,y-1);
        x*IntPowEfficient(x,y-1);
        x*IntPow(x,y-1);
        IntPow(x,y);
    }
}

// (x^a)^b == x^(a*b)
lemma IntPowPowLemma( x: int, a: int, b: int )
    decreases b
    requires x >= 0 && a >= 0 && b >= 0
    ensures IntPow(IntPow(x,a),b) == IntPow(x,a*b)
{
    if b == 0 { return; }
    IntPowPowLemma(x,a,b-1);
    IntPowMulLemma(x,a,a*(b-1));
    calc ==
    {
        IntPow(IntPow(x,a),b);
        IntPow(x,a)*IntPow(IntPow(x,a),b-1);
        IntPow(x,a)*IntPow(x,a*(b-1));
        IntPow(x,a+a*(b-1));
    }
}

// Integer raising to a power using the Russian peasant method in a loop.
method IntPowLoop( x: int, y: int) returns ( p: int )
    requires x >= 0
    requires y >= 0
    ensures p == IntPow(x,y)
{
    p := 1;
    var q, r := x, y;
    ghost var qpow, ppow := 1, 0;
    while r != 0
        invariant 0 <= r
        decreases r
        invariant qpow >= 1
        invariant ppow >= 0
        invariant q == IntPow(x,qpow)
        invariant p == IntPow(x,ppow)
        invariant y == ppow+r*qpow
    {
        if r%2 == 0
        {
            IntPowPowLemma(x,2*qpow,r/2);
            IntPowMulLemma(x,qpow,qpow);
            q, qpow, r := q*q, 2*qpow, r/2;
        }
        else
        {
            IntPowMulLemma(x,ppow,qpow);
            p, ppow, r := p*q, ppow+qpow, r-1;
        }
    }
}