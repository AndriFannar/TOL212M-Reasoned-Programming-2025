// Computing modular powers.
// Author: Snorri Agnarsson, snorri@hi.is, 2020-2024

include "IntPow.dfy"

lemma MultipleGE( x: int, y: int )
	requires y >= 1
	requires x >= 0
	ensures x*y >= x
{}

lemma MultipleLE( x: int, y: int )
	requires y <= -1
	requires x >= 0
	ensures x*y <= -x
{}

// If x == q*m+r and 0 <= r < m then q == x/m and r == x%m.
lemma ModBasicLemma( x: int, m: int, q: int, r: int )
	requires m > 0
    requires 0 <= r < m
    requires x == q*m+r
    ensures q == x/m
    ensures r == x%m
{
    var q2 := x/m;
    var r2 := x%m;
    if( q==q2 ) { return; }
	assert q!=q2;
    // Given that different quotients are possible,
    // we will now derive a contradiction
    assert m*(q-q2)+(r-r2) == 0;
    assert -m < r-r2 < m;
    if( q > q2 )
    {
        assert q-q2 >= 1;
		MultipleGE(m,q-q2);
		assert m*(q-q2) >= m;
        assert m*(q-q2)+(r-r2) != 0;
    }
    else
    {
        assert q-q2 <= -1;
		MultipleLE(m,q-q2);
		assert m*(q-q2) <= -m;
        assert m*(q-q2)+(r-r2) != 0;
    }
    /* Older version (does not work in current Dafny)
    var q2 := x/m;
    var r2 := x%m;
    if( q==q2 ) { return; }
    // Given that different quotients are possible,
    // we will now derive a contradiction.
    assert m*(q-q2)+(r-r2) == 0;
    assert -m < r-r2 < m;
    if( q > q2 )
    {
        assert q-q2 >= 1;
        assert m*(q-q2)+(r-r2) != 0;
    }
    else
    {
        assert q-q2 <= -1;
        assert m*(q-q2)+(r-r2) != 0;
    }
    */
}

// Modular addition
lemma AddMod( x: int, y: int, m: int )
    requires m > 0
    requires 0 <= x
    requires 0 <= y
    ensures (x+y)%m == ((x%m)+(y%m))%m
{
    if x%m+y%m < m 
    {
        ModBasicLemma(x+y,m,(x+y)/m,(x+y)%m);
        ModBasicLemma(x+y,m,x/m+y/m,x%m+y%m);
    }
    else
    {
        ModBasicLemma(x+y,m,(x+y)/m,(x+y)%m);
        ModBasicLemma(x+y,m,x/m+y/m+1,x%m+y%m-m);
    }
}

// Modular multiplication.
lemma ModMulLemma( x: int, y: int, m: int )
    requires m > 0
    requires x >= 0
    requires y >= 0
    ensures (x*y)%m ==
            (x*(y%m))%m ==
            ((x%m)*y)%m ==
            ((x%m)*(y%m))%m ==
            (y*(x%m))%m ==
            ((y%m)*x)%m ==
            ((y%m)*(x%m))%m
{
    ModMulHelperLemma(x,y,m);
    ModMulHelperLemma(x%m,y,m);
    ModMulHelperLemma(x,y%m,m);
    ModMulHelperLemma(x%m,y%m,m);
    ModMulHelperLemma(y,x,m);
    ModMulHelperLemma(y%m,x,m);
    ModMulHelperLemma(y,x%m,m);
    ModMulHelperLemma(y%m,x%m,m);
}

lemma ModMulHelperLemma( x: int, y: int, m: int )
    requires m > 0
    requires x >= 0
    requires y >= 0
    ensures (x*y)%m == (x*(y%m))%m
{
    ModBasicLemma(x*y,m,(x*y)/m,(x*y)%m);
    ModBasicLemma(x*y,m,x*(y/m)+(x*(y%m))/m,(x*(y%m))%m);
}

lemma ModPowHelperLemma( x: int, y: int, m: int )
    decreases y
    requires m > 0
    requires y >= 0
    requires x >= 0
    ensures IntPow(x,y)%m == IntPow(x%m,y)%m
{
    if y == 0 { return; }
    ModPowHelperLemma(x,y-1,m);
    ModMulLemma(x,IntPow(x,y-1),m);
    ModMulLemma(x,IntPow(x%m,y-1),m);
}

// Integer multiplication is associative.
lemma MulAssociatesLemma( x: int, y: int, z: int )
    ensures x*y*z == (x*y)*z == x*(y*z)
{}

// Integer multiplication is commutative.
lemma MulCommutesLemma( x: int, y: int )
    ensures x*y == y*x
{}

// Integer addition is commutative.
lemma AddCommutesLemma( x: int, y: int )
    ensures x+y == y+x
{}

// Modular multiplication is associative.
lemma ModMulAssociatesLemma( x: int, y: int, z: int, m: int )
    requires m > 1
    requires x >= 0
    requires y >= 0
    requires z >= 0
    ensures ModMul(x,ModMul(y,z,m),m) == 
            (x*(y*z))%m == 
            ((x*y)*z)%m == 
            (x*y*z)%m ==
            ModMul(ModMul(x,y,m),z,m) == 
            (x*(y*z))%m == 
            ((x*y)*z)%m == 
            (x*y*z)%m
{
    ModMulLemma(x,y,m);
    ModMulLemma(y,z,m);
    ModMulLemma(x,y*z,m);
    ModMulLemma(x*y,z,m);
    MulAssociatesLemma(x,y,z);
}

// Modular powers.
lemma ModPowLemma( x: int, y: int, z: int, m: int )
    decreases z
    requires m > 0
    requires y >= 0
    requires z >= 0
    requires x >= 0
    ensures IntPow(x,y+z) == IntPow(x,y)*IntPow(x,z)
    ensures IntPow(x,y+z)%m ==
            ((IntPow(x%m,y)%m)*(IntPow(x%m,z)%m))%m ==
            IntPow(x%m,y+z)%m
{
    ModPowHelperLemma(x,y+z,m);
    ModPowHelperLemma(x,y,m);
    ModPowHelperLemma(x,z,m);
    ModMulLemma(IntPow(x,y),IntPow(x,z),m);
    if z == 0 { return; }
    ModPowHelperLemma(x,y+z-1,m);
    ModPowLemma(x,y,z-1,m);
    MulAssociatesLemma(IntPow(x,y),x,IntPow(x,z-1));
    ModMulLemma(x,IntPow(x,y+z-1),m);
    ModMulLemma(IntPow(x,y),IntPow(x,z-1),m);
}

// Define modular multiplication
function ModMul( x: int, y: int, m: int ): int
    requires x >= 0
    requires y >= 0
    requires m > 1
{
    (x*y)%m
}

// Define modular powers
function ModPow( x: int, y: int, m: int ): int
    decreases y
    requires m > 1
    requires x >= 0
    requires y >= 0
    ensures 0 <= ModPow(x,y,m) < m
{
    if y == 0 then
        1
    else
        ModMul(x,ModPow(x,y-1,m),m)
}

// Fast modular power using recursion
method ModPowRecursive( x: int, y: int, m: int ) returns ( p: int )
    decreases y
    requires m > 1
    requires 0 <= x < m
    requires y >= 0
    ensures 0 <= p < m
    ensures p == IntPow(x,y)%m
{
    if y == 0 { return 1; }
    if y%2 == 0
    {
        p := ModPowRecursive(x,y/2,m);
        p := ModSquare(p,m);
        ModMulLemma(IntPow(x,y/2),IntPow(x,y/2),m);
        ModPowLemma(x,y/2,y/2,m);
    }
    else
    {
        p := ModPowRecursive(x,y/2,m);
        ModMulLemma(x,IntPow(x,y/2),m);
        p := ModMul(p,ModMul(x,p,m),m);
        ModMulLemma(IntPow(x,y/2),IntPow(x,y/2+1),m);
        ModPowLemma(x,y/2,y/2+1,m);
        assert y == y/2+y/2+1;
    }
}

// Fast modular power using a loop
method ModPowLoop( x: int, y: int, m: int ) returns ( p: int )
    requires m > 1
    requires x >= 0
    requires y >= 0
    ensures 0 <= p < m
    ensures p == ModPow(x,y,m)
{
    p := 1;
    var q := x%m;
    var r := y;
    ghost var qpow := 1;
    ghost var ppow := 0;
    while r != 0
        decreases r
        invariant r >= 0
        invariant 0 <= q < m
        invariant 0 <= p < m
        invariant qpow > 0
        invariant ppow >= 0
        invariant q == ModPow(x,qpow,m)
        invariant p == ModPow(x,ppow,m)
        invariant y == ppow+qpow*r
    {
        if r%2 == 0
        {
            r := r/2;
            ModPowMulLemma(x,qpow,qpow,m);
            q := ModSquare(q,m);
            qpow := 2*qpow;
        }
        else
        {
            r := r-1;
            p := ModMul(p,q,m);
            ModPowMulLemma(x,ppow,qpow,m);
            ppow := ppow+qpow;
        }
    }
}

// Prove x*(y*z) == (x*y)*z mod m
lemma ModMulIsAssociative( x: int, y: int, z: int, m: int )
    requires m > 1
    requires x >= 0
    requires y >= 0
    requires z >= 0
    ensures ModMul(x,ModMul(y,z,m),m) == ModMul(ModMul(x,y,m),z,m)
{
    ModMulLemma(x,y*z,m);
    ModMulLemma(x*y,z,m);
    calc ==
    {
        ModMul(x,ModMul(y,z,m),m);
        ModMul(x,(y*z)%m,m);
        (x*((y*z)%m))%m;
        (x*(y*z))%m;
        assert x*(y*z) == (x*y)*z;
        ((x*y)*z)%m;
        (((x*y)%m)*z)%m;
        ModMul(ModMul(x,y,m),z,m);
    }
}

// Prove x^(y1+y2) == x^y1 * x^y2 mod m
lemma ModPowMulLemma( x: int, y1: int, y2: int, m: int )
    decreases y2
    requires m > 1
    requires x >= 0
    requires y1 >= 0
    requires y2 >= 0
    ensures ModPow(x,y1+y2,m) == ModMul(ModPow(x,y1,m),ModPow(x,y2,m),m)
{
    if y2 == 0 { return; }
    ModPowMulLemma(x,y1,y2-1,m);
    calc ==
    {
        ModPow(x,y1+y2,m);
        ModMul(x,ModPow(x,y1+y2-1,m),m);
        ModMul(x,ModMul(ModPow(x,y1,m),ModPow(x,y2-1,m),m),m);
        ModMul(x,ModMul(ModPow(x,y2-1,m),ModPow(x,y1,m),m),m);
        { ModMulIsAssociative(x,ModPow(x,y2-1,m),ModPow(x,y1,m),m); }
        ModMul(ModMul(x,ModPow(x,y2-1,m),m),ModPow(x,y1,m),m);
        ModMul(ModPow(x,y2,m),ModPow(x,y1,m),m);
        ModMul(ModPow(x,y1,m),ModPow(x,y2,m),m);
    }
}

// Define Modular squaring
function ModSquare( x: int, m: int ): int
    requires m > 1
    requires 0 <= x < m
    ensures ModSquare(x,m) == (x*x)%m
    ensures ModSquare(x,m) == ModPow(x,2,m)
    ensures ModSquare(x,m) == IntPow(x,2)%m
    ensures ModSquare(x,m) == ModMul(x,x,m)
{
    (x*x)%m
}

method Main()
{
    var z : int;
    var m := IntPowEfficient(2,607)-1;
    z := ModPowRecursive(3,10000000,m);
    assert z == IntPow(3,10000000)%m;
    print z;
    print "\n";
    z := ModPowLoop(3,10000000,m);
    print z;
    print "\n";
    z := ModPowRecursive(3,100000000,m);
    print z;
    print "\n";
    z := ModPowLoop(3,100000000,m);
    print z;
    print "\n";
}