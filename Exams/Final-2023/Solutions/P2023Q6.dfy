/*
Program the following Dafny function:

method Quickselect( a: multiset<int>, k: int )
  returns( b: multiset<int>, c: seq<int>, d: multiset<int> )
    requires 0 <= k < |a|
    ensures a == b+multiset(c)+d
    ensures |b| <= k < |b|+|c|
    ensures forall p,q | p in c && q in c :: p == q
    ensures forall p,q | p in b && q in c :: p <= q
    ensures forall p,q | p in d && q in c :: p >= q

You may use the Partition function as a helper function.
*/

include "P2023Q5.dfy"

method Quickselect( a: multiset<int>, k: int ) returns( b: multiset<int>, c: seq<int>, d: multiset<int> )
    requires 0 <= k < |a|
    ensures a == b+multiset(c)+d
    ensures |b| <= k < |b|+|c|
    ensures forall p, q | p in c && q in c :: p == q
    ensures forall p, q | p in b && q in c :: p <= q
    ensures forall p, q | p in d && q in c :: p >= q
{
    b, c, d := Partition(a);
    if |b| <= k < |b|+|c| { return; }
    if k < |b|
    {
        var b', c', d' := Quickselect(b,k);
        //  
        //  |       b      | c |  d  |
        //  | b' | c' | d' |
        //         ^
        //         k
        //

        // The following asserts are not necessary in order for this to be correct,
        // but Dafny needs them
        assert forall p, q | p in c && q in c' :: q in b && p >= q;
        assert forall p, q | p in d && q in c' :: q in b && p >= q;
        assert forall z | z in d'+multiset(c)+d :: z in d' || z in c || z in d;

        d := d'+multiset(c)+d;
        b := b';
        c := c';
    }
    else
    {
        // k >= |b|+|c|
        var b', c', d' := Quickselect(d,k-|b|-|c|);
        // 
        //  |  b  | c |       d      |
        //            | b' | c' | d' |
        //                   ^
        //                   k
        //

        // The following asserts are not necessary in order for this to be correct,
        // but Dafny needs them
        ghost var p :| p in c';
        assert p in d;
        assert forall p, q | p in c && q in c' :: q in d && p <= q;
        assert forall p, q | p in b && q in c' :: q in d && p <= q;
        assert forall z | z in b+multiset(c)+b' :: z in b || z in c || z in b';

        b := b+multiset(c)+b';
        c := c';
        d := d';
    }
}