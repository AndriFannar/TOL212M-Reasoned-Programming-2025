// This include fetches the Partition method
include "P1-4.dfy"  

method Sort( s: seq<int> ) returns( r: seq<int> )
    decreases |s|
    ensures multiset(r) == multiset(s)
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
{
    if |s| < 2 { return s; }
    var a,p,b,q,c := Partition(s);

    // Not needed for human readers:
    assert multiset(a) <= multiset(s)-multiset{p,q};
    assert |a| == |multiset(a)|;
    assert |a| <= |s|-2;
    assert |b| <= |s|-2;
    assert |c| <= |s|-2;

    var a' := Sort(a);
    var b' := Sort(b);
    var c' := Sort(c);
    r := a'+[p]+b'+[q]+c';

    // Not needed for human readers:
    assert forall i | 0 <= i < |a'| :: r[i] in multiset(a) && r[i] in a;
    assert forall i | |a'| < i < |a'+[p]+b'| :: r[i] in multiset(b);
    assert forall i | |a'| < i < |a'+[p]+b'| :: r[i] in multiset(b) && r[i] in b;
    assert forall i | |a'+[p]+b'| < i < |r| :: r[i] in multiset(c) && r[i] in c;
}