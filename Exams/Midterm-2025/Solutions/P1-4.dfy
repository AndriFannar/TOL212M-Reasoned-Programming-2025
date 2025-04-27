method Partition( s: seq<int> )
        returns ( a: seq<int>
                , p: int
                , b: seq<int>
                , q: int
                , c: seq<int>
                )
    requires |s| >= 2
    ensures p <= q
    ensures multiset(s) ==
                multiset(a)+
                multiset{p}+
                multiset(b)+
                multiset{q}+
                multiset(c)
    ensures forall z | z in a :: z < p
    ensures forall z | z in b :: p <= z <= q
    ensures forall z | z in c :: z > q
{
    if |s| == 2
    {
        a,b,c := [],[],[];
        p,q := s[0],s[1];

        // Not needed for human readers:
        assert s == s[..1]+s[1..];
        assert multiset(s) == multiset{p,q};

        if p > q { p,q := q,p; }
        return;
    }

    // Not needed for human readers:
    assert s == s[..1]+s[1..];
    assert multiset(s) == multiset(s[..1])+multiset(s[1..]);

    a,p,b,q,c := Partition(s[1..]);
    if s[0] < p      { a := a+[s[0]]; }
    else if s[0] > q { c := c+[s[0]]; }
    else             { b := b+[s[0]]; }
    
    /*
    // Loop solution body
    p, q := s[0], s[1];
    a, b, c := [], [], [];
    
    // Not needed for human readers:
    assert s[..2] == s[..1]+s[1..2];
    assert multiset(s[..2]) == multiset{s[0],s[1]};
    assert multiset{p,q} == multiset(s[..2]);

    if p > q { p,q := q,p; }

    // Not needed for human readers:
    assert multiset{p,q} == multiset(s[..2]);

    var i := 2;
    while i < |s|
        decreases |s|-i;
        invariant 2 <= i <= |s|;
        invariant p <= q;
        invariant multiset(s[..i]) ==
                    multiset(a)+
                    multiset{p}+
                    multiset(b)+
                    multiset{q}+
                    multiset(c);
        invariant forall z | z in a :: z < p;
        invariant forall z | z in b :: p <= z <= q;
        invariant forall z | z in c :: z > q;
    {
        if s[i] < p      { a := a+[s[i]]; }
        else if s[i] > q { c := c+[s[i]]; }
        else             { b := b+[s[i]]; }
        i := i+1;

        // Not needed for human readers:
        assert s[..i] == s[..i-1]+s[i-1..i];
    }
    // Not needed for human readers:
    assert s == s[..i];
    */    
}