method Search100( a: array<int> ) returns ( k: int )
    requires forall p,q | 0 <= p < q < a.Length :: a[p] <= a[q]
    ensures k == -1 ==>
        forall r | 0 <= r < a.Length :: a[r] >= 100
    ensures k != -1 ==>
        (0 <= k < a.Length) &&
        (forall r | 0 <= r <= k :: a[r] < 100) &&
        (forall r | k < r < a.Length :: a[r] >= 100)
{
    var i,j := 0,a.Length;
    while i != j
        decreases j-i
        invariant 0 <= i <= j <= a.Length
        invariant forall r | 0 <= r < i :: a[r] < 100
        invariant forall r | j <= r < a.Length :: a[r] >= 100
    {
        var m := i+(j-i)/2;
        if a[m] < 100 { i := m+1; }
        else          { j := m;   }
    }
    if i == 0 { return -1; }
    k := i-1;
}