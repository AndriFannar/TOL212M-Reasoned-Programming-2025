// Author of question: Snorri Agnarsson
// Permalink of question: https://tinyurl.com/mssdpfvr

// Author of solution:    ...
// Permalink of solution: ...

method SearchRecursive( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|
    ensures i <= k < j || k == -1
    ensures k != -1 ==> a[k] == x
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
{
    if i == j { return -1; }
    if a[j-1] == x { return j-1; }
    k := SearchRecursive(a,i,j-1,x);
}

method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|
    ensures i <= k < j || k == -1
    ensures k != -1 ==> a[k] == x
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
{
    var p := j;
    while p > i 
        invariant i <= p <= j
        invariant forall q | p <= q < j :: a[q] != x
        // Fastayrðing lykkju/Loop invariant:
        //    a: | ??? | allt/all !=x |
        //        i     p              j
    {
        p := p-1;
        if a[p] == x { return p; }
    }
    return -1;   
}