// Author: Snorri Agnarsson.

// Permalink: https://tinyurl.com/3sn8b8a9

// Lemma for proving termination of bisection methods.
// Helps prove that halving the interval size in each
// step will inevitably cause the interval size to 
// eventually become smaller that eps, assuming eps>0.
lemma BisectionTermination( x: real, y: real, eps: real )
    requires eps > 0.0
    requires x >= eps > 0.0
    requires y == x/2.0
    ensures (x/eps).Floor > (y/eps).Floor
{
    assert y/eps == x/eps/2.0;
    if (x/eps).Floor == 1 { assert 1.0 <= x/eps < 2.0; }
    else                  { assert x/eps >= 2.0;       }
}

method RootRecursive( f: (real)->real, a: real, b: real, eps: real ) returns( r: real )
    requires a <= b
    requires eps > 0.0
    requires f(a)*f(b) <= 0.0
    decreases ((b-a)/eps).Floor
    ensures exists s,t: real | a <= s <= r <= t <= b :: (t-s) < eps && f(t)*f(s) <= 0.0
{
    if b-a < eps { return a; }
    var m := (a+b)/2.0;

    // Proving termination
    BisectionTermination(b-a,m-a,eps);
    BisectionTermination(b-a,b-m,eps);
    // Proving precondition
    assert f(a)*f(m) > 0.0 ==> f(m)/f(a) > 0.0 && f(m)*f(b) == f(a)*f(b)*(f(m)/f(a)) <= 0.0;

    if f(a)*f(m) <= 0.0 { r := RootRecursive(f,a,m,eps); }
    else                { r := RootRecursive(f,m,b,eps); }
}

method RootLoop( f: (real)->real, a: real, b: real, eps: real ) returns( r: real )
    requires a <= b
    requires eps > 0.0
    requires f(a)*f(b) <= 0.0
    ensures exists s,t: real | a <= s <= r <= t <= b :: (t-s) < eps && f(t)*f(s) <= 0.0
{
    var p,q := a,b;
    while q-p >= eps
        invariant a <= p <= q <= b
        invariant f(p)*f(q) <= 0.0
        decreases ((q-p)/eps).Floor
    {
        var m := (q+p)/2.0;

        // Proving termination
        BisectionTermination(q-p,m-p,eps);
        BisectionTermination(q-p,q-m,eps);
        // Proving invariant
        assert f(p)*f(m) > 0.0 ==> f(m)/f(p) > 0.0 && f(m)*f(q) == f(p)*f(q)*(f(m)/f(p)) <= 0.0;

        if f(p)*f(m) <= 0.0 { q := m; }
        else                { p := m; }
    }
    return p;
}

method MinimumRecursive( f:(real)->real, a: real, b: real, c: real, eps: real ) returns( r: real )
    requires a < b < c
    requires eps > 0.0
    requires b == (a+c)/2.0
    requires f(b) <= f(a) && f(b) <= f(c)
    ensures exists s,t | a <= s < r < t <= c ::
        t-s < eps && f(r) <= f(s) && f(r) <= f(t)
    decreases ((c-a)/eps).Floor
{
    if c-a < eps { return b; }
    var m1, m2 := (a+b)/2.0, (b+c)/2.0;

    // Proving termination
    BisectionTermination(c-a,b-a,eps);
    BisectionTermination(c-a,m2-m1,eps);
    BisectionTermination(c-a,c-b,eps);

    if f(m1) <= f(b)      { r := MinimumRecursive(f,a,m1,b,eps);  }
    else if f(m2) <= f(b) { r := MinimumRecursive(f,b,m2,c,eps);  }
    else                  { r := MinimumRecursive(f,m1,b,m2,eps); }
}

method MinimumLoop( f:(real)->real, a: real, b: real, c: real, eps: real ) returns( r: real )
    requires a < b < c
    requires eps > 0.0
    requires b == (a+c)/2.0
    requires f(b) <= f(a) && f(b) <= f(c)
    ensures exists s,t | a <= s < r < t <= c ::
        t-s < eps && f(r) <= f(s) && f(r) <= f(t)
{
    var t,u,v := a,b,c;
    while v-t >= eps
        invariant a <= t < u < v <= c
        invariant u == (t+v)/2.0
        invariant f(u) <= f(t) && f(u) <= f(v)
        decreases ((v-t)/eps).Floor
    {
        var m1, m2 := (t+u)/2.0, (u+v)/2.0;

        // Proving termination
        BisectionTermination(v-t,v-u,eps);
        BisectionTermination(v-t,m2-m1,eps);
        BisectionTermination(v-t,u-t,eps);

        if f(m1) <= f(u)      { u,v := m1,u;  }
        else if f(m2) <= f(u) { t,u := u,m2;  }
        else                  { t,v := m1,m2; }
    }
    return u;
}

method Pow( x: real, n: int ) returns( r: real )
    requires n >= 0
	decreases n
    ensures x > 0.0 ==> r > 0.0
{
    if n==0 { return 1.0; }
    r := Pow(x,n-1);
    r := x*r;
}

method Main()
{
    var eps := Pow(0.1,41);
    var f := (x)=>x*x-10.0;
	assert 
		3.0 < 4.0 && 
		f(3.0)*f(4.0) <= 0.0;
    var r := RootRecursive(f,3.0,4.0,eps);
    assert exists a,b :: 
		3.0 <= a <= r <= b <= 4.0 && 
		b-a < eps && 
		f(a)*f(b) <= 0.0;
    print r;
    print " =\n";
    var s := ShowReal(r,40);
    print s;
    print " \n";
    f := (x)=>x*x-2.0;
	assert 
		1.0 < 2.0 && 
		f(1.0)*f(2.0) <= 0.0;
    r := RootLoop(f,1.0,2.0,eps);
    assert exists a,b :: 
		1.0 <= a <= r <= b <= 2.0 && 
		b-a < eps && 
		f(a)*f(b) <= 0.0;
    print r;
    print " =\n";
    s := ShowReal(r,40);
    print s;
    print "\n";
    f := (x)=>x*x*x/3.0-2.0*x;
	assert
		1.0 < 2.0 && 
		1.5 == (1.0+2.0)/2.0 && 
		f(1.5) <= f(1.0) && 
		f(1.5) <= f(2.0);
    r := MinimumLoop(f,1.0,1.5,2.0,eps);
    assert exists a,b ::
		1.0 <= a < r < b <= 2.0 &&
		b-a < eps && 
		f(r) <= f(a) && 
		f(r) <= f(b);
    r := MinimumRecursive(f,1.0,1.5,2.0,eps);
    assert exists a,b ::
		1.0 <= a < r < b <= 2.0 && 
		b-a < eps && 
		f(r) <= f(a) && 
		f(r) <= f(b);
    print r;
    print " =\n";
    s := ShowReal(r,40);
    print s;
    print "\n";
}

method ShowReal( x: real, n: int ) returns( s: string )
    requires n >= 0
    requires x >= 0.0
{
    s := ShowInt(x.Floor);
    s := s+".";
    var z := x-(x.Floor as real);
    var i := 0;
    while i != n 
        invariant 0 <= i <= n
        invariant 0.0 <= z < 1.0
        decreases n-i
    {
        z := z*10.0;
        var next := z.Floor;
        s := s+["0123456789"[next]];
        i := i+1;
        z := z - (next as real);
    }
}

method ShowInt( x: int ) returns( s: string )
    requires x >= 0
{
    if x < 10 { return ["0123456789"[x]]; }
    s := ShowInt(x/10);
    s := s+["01234567890"[(x%10)]];
}