method Loka2( a: array<int>, i: int, j: int ) returns ( k: int )
    decreases j-i
    requires 0 <= i <= j <= a.Length
    requires forall p,q | i <= p < q < j :: a[p] >= a[q]
    ensures k == -1 ==> forall r | i <= r < j :: a[r] >= 100
    ensures k != -1 ==>
        (i <= k < j) &&
        (forall r | i <= r < k :: a[r] >= 100) &&
        (forall r | k <= r < j :: a[r] < 100)
{
    if i==j { return -1; }
    var m := i+(j-i)/2;
    if a[m] < 100
    {
        k := Loka2(a,i,m);
        if k == -1 { k := m; }
    }
    else
    {
        k := Loka2(a,m+1,j);
    }
}