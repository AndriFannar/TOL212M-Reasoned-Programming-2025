// Author of question:  Snorri Agnarsson, snorri@hi.is

// Author of solution:       ...
// Permalink of solution:    ...

// Finish programminng the two methods

method Partition( m: multiset<int> )
        returns( pre: multiset<int>, p: int, post: multiset<int> )
    requires |m| > 0
    ensures p in m
    ensures m == pre+multiset{p}+post
    ensures forall z | z in pre :: z <= p
    ensures forall z | z in post :: z >= p
{
    // The body is missing.
    // You can use a loop or recursion.
}

method QuickSelect( m: multiset<int>, k: int )
        returns( pre: multiset<int>, kth: int, post: multiset<int> )
    requires 0 <= k < |m|
    ensures kth in m
    ensures m == pre+multiset{kth}+post
    ensures |pre| == k
    ensures forall z | z in pre :: z <= kth
    ensures forall z | z in post :: z >= kth
{
    // The body is missing.
    // You can use a loop or recursion.
    // Use the Partition method as a helper method.
}