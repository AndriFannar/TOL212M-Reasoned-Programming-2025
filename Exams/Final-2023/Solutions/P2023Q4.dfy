/*
Assume a Dafny function with the following description:

method Partition( a: multiset<int> )
     returns( b: multiset<int>, c: seq<int>, d: multiset<int> )
   requires |a| > 0;
   ensures exists p | p in a ::
        (forall z | z in b :: z <= p) &&
        (forall z | z in c :: z == p) &&
        (forall z | z in d :: z >= p);
    ensures a == b+multiset(c)+d;
    ensures |c| > 0;

Write a Quicksort function that uses this function as a helper function to
transform a multiset into a sorted sequence of the same values. Do not 
program the Partition function here.
*/

include "P2023Q5.dfy"

predicate IsSorted( s: seq<int> )
{
    forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
}

method QuickSort( a: multiset<int> ) returns( s: seq<int> )
    ensures multiset(s) == a 
    ensures IsSorted(s)
{
    if a == multiset{} { return []; }
    var b, c, d := Partition(a);
    var b' := QuickSort(b);
    var d' := QuickSort(d);
    s := b'+c+d';

    // The following is only needed for Dafny to recognize correctness.
    // It is not needed for human readers.
    ghost var p :| p in c;
    assert forall z | z in c :: z == p;
    assert forall z | z in b' :: z in b;
    assert forall z | z in b' :: z in b && z <= p;
    assert forall z | z in d' :: z in d && z >= p;
    assert forall x | x in c :: x == p;
    assert forall x, y | x in b' && x in b && y in c :: x <= y;
    assert forall x | x in d' :: x in d;
    assert forall x, y | x in c && y in d' :: y in d && x <= y;
    assert forall p | 0 <= p < |b'| :: s[p] == b'[p];
    assert forall p, q | 0 <= p < q < |b'| :: s[p] == b'[p] && s[q] == b'[q];
    assert forall p, q | 0 <= p < q < |b'| :: s[p] == b'[p] && s[q] == b'[q] && b'[p] <= b'[q];
    assert forall p, q | 0 <= p < q < |b'| :: s[p] == b'[p] && s[q] == b'[q] && b'[p] <= b'[q] && s[p] <= s[q];
    assert forall i | 0 <= i < |b'| :: s[i] in b && s[i] in b';
    assert forall i | |b'| <= i < |b'+c| :: s[i] in c;
    assert forall i | |b'+c| <= i < |s| :: s[i] in d && s[i] in d';
    assert forall p | 0 <= p < |s| :: s[p] in b' || s[p] in c || s[p] in d';
}