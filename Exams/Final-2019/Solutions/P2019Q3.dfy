predicate IsTwoPow( n: int )
    requires n > 0
{
    n==1 || (n%2==0 && IsTwoPow(n/2))
}

method Find( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    decreases n
    requires 0 <= i <= i+n <= a.Length
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q]
    requires IsTwoPow(n+1)
    ensures i <= k <= i+n
    ensures forall p | i <= p < k :: a[p] < x
    ensures forall p | k <= p < i+n :: a[p] >= x
{
    if n==0 { return i; }
    if a[i+n/2] < x
    {
        k := Find(a,i+n/2+1,n/2,x);
    }
    else
    {
        k := Find(a,i,n/2,x);
    }
}