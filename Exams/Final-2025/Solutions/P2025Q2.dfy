method P2025Q2( a: seq<int> ) returns( k: int )
    decreases |a|
    requires forall p, q | 0 <= p < q < |a| :: a[p] >= a[q]
    ensures -1 <= k < |a|
    ensures forall r | 0 <= r <= k :: a[r] > 2025
    ensures forall r | k < r < |a| :: a[r] <= 2025
{
    if a == [] {return -1; }
    var m := |a|/2;
    if a[m] <= 2025
    {
        k := P2025Q2(a[..m]);
    }
    else
    {
        k := P2025Q2(a[m+1..]);
        k := k+m+1;
    }
}

method P2025Q2b( a: seq<int>, i: int, j: int ) returns( k: int )
    decreases j-i 
    requires 0 <= i <= j <= |a|
    requires forall p, q | 0 <= p < q < |a| :: a[p] >= a[q]
    ensures k == -1 ==> forall r | i <= r < j :: a[r] <= 2025
    ensures k != -1 ==> i <= k < j 
    ensures k != -1 ==> forall r | i <= r <= k :: a[r] > 2025 
    ensures k != -1 ==> forall r | k < r < j :: a[r] <= 2025
{
    if i==j { return -1; }
    var m := i+(j-i)/2;
    if a[m] <= 2025
    {
        k := P2025Q2b(a,i,m);
    }
    else
    {
        k := P2025Q2b(a,m+1,j);
        if k == -1 { k := m; }
    }
}
