/*
Write a recursive binary search method in Dafny that searches in a
section of an integer array that is in descending order for the
rightmost position that contains a positive number. If no such 
position exists return -1.
*/

method FindLastPositive( a: array<int> ) returns( k: int )
    requires forall p, q | 0 <= p < q < a.Length :: a[p] >= a[q]
    ensures k == -1 ==> forall z | z in a[..] :: z <= 0
    ensures k != -1 ==>
        0 <= k < a.Length &&
        a[k] > 0 &&
        forall i | k < i < a.Length :: a[i] <= 0
{
    k := FindLastPositiveHelp(a,0,a.Length);
    assert a[..] == a[0..a.Length];   // Only needed to convince Dafny, not needed for human readers
}

method FindLastPositiveHelp( a: array<int>, i: int, j: int ) returns( k: int )
    requires 0 <= i <= j <= a.Length
    decreases j-i
    requires forall p, q | 0 <= p < q < a.Length :: a[p] >= a[q]
    ensures k != -1 ==>
        i <= k < j &&
        a[k] > 0 &&
        forall r | k+1 <= r < j :: a[r] <= 0
    ensures k == -1 ==> forall r | i <= r < j :: a[r] <= 0
{
    if i == j { return -1; }
    var m := i+(j-i)/2;
    if a[m] > 0
    {
        k := FindLastPositiveHelp(a,m+1,j);
        if k == -1 { k := m; }
    }
    else
    {
        k := FindLastPositiveHelp(a,i,m);
    }
}