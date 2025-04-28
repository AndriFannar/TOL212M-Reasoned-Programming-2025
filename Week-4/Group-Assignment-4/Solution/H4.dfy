// Author of question:   Snorri Agnarsson, snorri@hi.is

// Author of solution:     Snorri Agnarsson
// Permalink of solution:  https://tinyurl.com/y4sj3duy

// Note that the solution that the URL refers to is slightly
// modified so that tio.run can compile and run it.

///////////////////////////////////////////////////////////////
// This is the start of the part of the file that should not
// be changed. Following that part is the part you should 
// change.
///////////////////////////////////////////////////////////////

// IsSorted(a) er satt þá og því aðeins að
// sannað sé að a sé raðað í vaxandi röð.
// IsSorted(a) is true if and only if it is
// proven that a is in ascending order.
predicate IsSorted( a: seq<int> )
{
    forall p,q | 0 <= p < q < |a| :: a[p] <= a[q]
}

// IsSegmented(a,b) er satt þá og því aðeins að
// sannað sé að öll gildi í a séu <= öll gildi í b.
// IsSegmented(a,b) is true if and only if it is
// proven that all values in a are <= all values in b.
predicate IsSegmented( a: seq<int> , b: seq<int> )
{
    (forall z,w | z in a && w in b :: z <= w) &&
    (forall p,q | 0 <= p < |a| && 0 <= q < |b| :: a[p] <= b[q])
}

// SortedEquals(a,b) sannar, fyrir raðaðar runur
// a og b, sem innihalda sama poka gilda, að runurnar
// eru jafnar.
// SortedEquals(a,b) proves that for sorted squences
// a and b that contain the same multiset of values,
// that the sequences are equal.
lemma SortedEquals( a: seq<int>, b: seq<int> )
    requires multiset(a) == multiset(b)
    requires IsSorted(a)
    requires IsSorted(b)
    ensures a == b
{
    if a == []
    {
        assert |b| == 0 || b[0] in multiset(a);
        return;
    }
    if b == []
    {
        assert |a| == 0 || a[0] in multiset(b);
        return;
    }
    assert a[0] in multiset(b);
    assert b[0] in multiset(a);
    assert a == a[0..1]+a[1..];
    assert b == b[0..1]+b[1..];
    assert a[0] == b[0];
    assert multiset(a[1..]) == multiset(a)-multiset{a[0]};
    assert multiset(b[1..]) == multiset(b)-multiset{b[0]};
    SortedEquals(a[1..],b[1..]);
}

// Samröðunarfall sem nota má í röksemdafærslu
// en ekki í raunverulegum útreikningum.
// A merge function that can be used in reasoning
// but not for real computations.
function MergeFun( a: seq<int>, b: seq<int> ): seq<int>
    decreases |a|+|b|
{
    if a == [] then
        b
    else if b == [] then
        a
    else if a[0] <= b[0] then
        [a[0]]+MergeFun(a[1..],b)
    else
        [b[0]]+MergeFun(a,b[1..])
}

// Sannar að MergeFun(a,b) skilar réttu gildi.
// Fyrir mannlega lesendur er það augljóst,
// en Dafny þarf smá hjálp til að sanna það
// með þrepasönnun. Þið munuð vilja kalla á
// þessa hjálparsetningu ef þið byggið ykkar
// samröðun á endurkvæmni.
// Proves that MergeFun(a,b) returns the
// correct value. For human readers this is
// obvious but Dafny needs a little help to
// prove this using induction. You will wish
// to call this lemma if you base your merge
// on recursion.
lemma MergeFunWorks( a: seq<int>, b: seq<int>, c: seq<int> )
    decreases |a|+|b|
    requires IsSorted(a)
    requires IsSorted(b)
    requires c == MergeFun(a,b)
    ensures multiset(c) == multiset(a)+multiset(b)
    ensures IsSorted(c)
    ensures a!=[] && b!=[] && a[0]<=b[0] ==> c==a[0..1]+MergeFun(a[1..],b)
    ensures a!=[] && b!=[] && a[0]>=b[0] ==> c==b[0..1]+MergeFun(a,b[1..])
{
    if a == [] || b == [] { return; }
    if a[0] <= b[0]
    {
        MergeFunWorks(a[1..],b,c[1..]);
        calc ==
        {
            multiset(c);
            multiset(c[0..1]+c[1..]);
            multiset(c[0..1])+multiset(c[1..]);
            multiset(c[0..1])+multiset(a[1..])+multiset(b);
            multiset(a[0..1])+multiset(a[1..])+multiset(b);
            multiset(a[0..1]+a[1..])+multiset(b);
            assert a[0..1]+a[1..] == a;
            multiset(a)+multiset(b);
        }
    }
    else
    {
        MergeFunWorks(a,b[1..],c[1..]);
        calc ==
        {
            multiset(c);
            multiset(c[0..1]+c[1..]);
            multiset(c[0..1])+multiset(c[1..]);
            multiset(c[0..1])+multiset(a)+multiset(b[1..]);
            multiset(b[0..1])+multiset(a)+multiset(b[1..]);
            multiset(a)+multiset(b[0..1])+multiset(b[1..]);
            multiset(a)+multiset(b[0..1]+b[1..]);
            assert b[0..1]+b[1..] == b;
            multiset(a)+multiset(b);
        }
    }
}

// Sannar að poki með einu staki samsvarar runu
// með einu staki.  Dafny þarf smávegis olnbogaskot
// til að fatta það. Þetta er gagnlegt til að sanna
// að útkoman úr Sort sé rétt í sértilvikinu þegar
// raðað er poka m með aðeins einu gildi x, sem
// gefur þá rununa s == [x].
// Proves that a multiset with one element corresponds
// to a sequence with one value. Dafny needs a little
// help to realize this. This is useful to prove that
// the result from Sort is correct in the special case
// where we are sorting a multiset m with only one value
// x which then gives the sequence s == [x].
lemma Singleton( m: multiset<int>, s: seq<int>, x: int )
    requires x in m
    requires x in s
    requires |s| == 1 == |m|
    ensures |m-multiset{x}| == 0
    ensures s == [x]
    ensures m == multiset{x}
    ensures m == multiset(s)
    ensures IsSorted(s)
{}

// Fjarlægir tvö gildi úr poka.  Getur verið gagnlegt
// í Split fallinu.
// Removes two values from a multiset. Can be useful
// in the Split function.
method RemoveTwo( a: multiset<int> ) returns( b: multiset<int>, x: int, y: int )
    requires |a| >= 2
    ensures a == b+multiset{x,y}
{
    b := a;
    x :| x in b;
    b := b-multiset{x};
    assert |b| >= 1;
    y :| y in b;
    b := b-multiset{y};
}

// Prófunarfall sem staðfestir að Split og Sort
// séu áreiðanlega að virka sannanlega rétt.
// Alls ekki má breyta þessu falli.  Athugið að
// þetta fall skilgreinir í raun þá virkni sem
// Split og Sort eiga að hafa, þ.e. forskilyrði
// og eftirskilyrði þeirra falla.
// A test function that validates that Split and
// Sort are provably correct. This function must not
// be modified. Notice that this function does in
// fact define the functionality that Split and
// Sort should have, i.e. the preconditions and
// postcoditions of those functions.
method Test( x: multiset<int> )
{
    var a,b := Split(x);
    assert a+b == x;
    assert (|a|==|b|) || (|a|==|b|+1);
    a,b := Split(x);
    assert a+b == x;
    assert (|a|==|b|) || (|a|==|b|+1);
    var c := Sort(x);
    assert multiset(c) == x;
    assert IsSorted(c);
}

// Aðalforritið er óþarfi, en er sett hér til gamans
// svo hægt sé að keyra eitthvað.
// The Main function is not necessary but is put here
// for fun so we have something to run.
method Main()
{
    var x := Sort(multiset{0,9,1,8,2,7,3,6,4,5
                          ,0,9,1,8,2,7,3,6,4,5
                          }
                 );
    print x;    
}

///////////////////////////////////////////////////////////////
// This is the end of the unchangable part of the file.
// Following this is the part you should modify in order to
// implements a version of merge sort.
///////////////////////////////////////////////////////////////

// Þið munuð vilja nota þetta samröðunarfall í Sort fallinu.
// You will want to use this merge method in the Sort method.
method Merge( a: seq<int>, b: seq<int> ) returns( c: seq<int> )
    requires IsSorted(a)
    requires IsSorted(b)
    ensures IsSorted(c)
    ensures multiset(a)+multiset(b) == multiset(c)
    ensures c == MergeFun(a,b)
{
    /*
    // Recursive version:
    if a == [] { return b; }
    if b == [] { return a; }
    if a[0] <= b[0]
    {
        c := Merge(a[1..],b);
        c := a[0..1]+c;
        MergeFunWorks(a,b,c);
    }
    else
    {
        c := Merge(a,b[1..]);
        c := b[0..1]+c;
        MergeFunWorks(a,b,c);
    }
    */
    
    // Loop version:
    c := [];
    var a', b' := a, b;
    while a' != [] && b' != []
        decreases |a'|+|b'|
        invariant IsSorted(a') && IsSorted(b') && IsSorted(c)
        invariant IsSegmented(c,a') && IsSegmented(c,b')
        invariant multiset(a)+multiset(b) == multiset(c)+multiset(a')+multiset(b')
    {
        assert a' == a'[0..1]+a'[1..] && b' == b'[0..1]+b'[1..];
        if a'[0] <= b'[0] { c, a' := c+a'[0..1], a'[1..]; }
        else              { c, b' := c+b'[0..1], b'[1..]; }
    }
    c := c+a'+b';
    MergeFunWorks(a,b,MergeFun(a,b));
    SortedEquals(c,MergeFun(a,b));
}

// Skiptir innihaldi poka í tvennt þannig að pokarnir
// sem koma út eru nokkurn veginn jafn stórir.
// Split the contents of a multiset in two such that
// the resulting multisets are approximately of equal
// size.
method Split( a: multiset<int> )
        returns ( b: multiset<int>
                , c: multiset<int>
                )
    decreases a
    ensures a == b+c
    ensures |b| == |c| || |b| == |c|+1
{
    /*
    // Recursive solution:
    if |a| < 2 { return a, multiset{}; }
    var rest,x,y := RemoveTwo(a);
    b, c := Split(rest);
    b := b+multiset{x};
    c := c+multiset{y};
    */
    // Loop solution:
    var rest := a;
    var x, y: int;
    b := multiset{};
    c := multiset{};
    while |rest| >= 2
        invariant a == b+c+rest
        invariant |b| == |c|
        decreases rest
    {
        rest, x, y := RemoveTwo(rest);
        b := b+multiset{x};
        c := c+multiset{y};
    }
    b := b+rest;
}

method Sort( a: multiset<int> ) returns ( b: seq<int> )
    decreases |a|
    ensures a == multiset(b)
    ensures IsSorted(b)
{
    if |a| == 0 { return []; }
    if |a| == 1
    {
        var x :| x in a;
        Singleton(a,[x],x);
        return [x];
    }
    var c, d := Split(a);
    var e := Sort(c);
    var f := Sort(d);
    b := Merge(e,f);
}