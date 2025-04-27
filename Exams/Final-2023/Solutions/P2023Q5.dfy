method Partition( a: multiset<int> )
     returns( b: multiset<int>, c: seq<int>, d: multiset<int> )
   requires |a| > 0
   ensures exists p | p in a ::
        (forall z | z in b :: z <= p) &&
        (forall z | z in c :: z == p) &&
        (forall z | z in d :: z >= p)
    ensures a == b+multiset(c)+d
    ensures |c| > 0
{
    var x :| x in a;
    var a' := a-multiset{x};
    if a' == multiset{} { return multiset{},[x],multiset{}; }
    b, c, d := Partition(a-multiset{x});
    var p :| p in c;
    if x < p      { b := b+multiset{x}; }
    else if x > p { d := d+multiset{x}; }
    else          { c := c+[x];         }
}