// Usage: k := BinarySearchAnyEQ(a,x);
// Pre:   a is a seq<int> that is in ascending order, x is an int
// Post:  If x exists in a then 0 <= k < |a| and a[k] == x.
//        Otherwise, k < 0 and 0 <= -k-1 <= |a| and
//        all values in a[..-k-1] (this is exclusive of a[-k-1])
//        are < x and all values in a[-k-1..] are > x.
//
//        So one of these two pictures hold:
//
//        a: | <= x |x| >= x |
//            ^      ^        ^
//            0      k       |a|
//
//        a: |  < x  |  > x  |
//            ^       ^       ^
//            0     -k-1     |a|
//
method BinarySearchAnyEQ( a: seq<int>, x: int ) returns( k: int )
    requires forall p,q | 0 <= p < q < |a| :: a[p] <= a[q]
    ensures x in a ==> 0 <= k < |a|
    ensures x in a ==> a[k] == x
    ensures x !in a ==> 0 <= -k-1 <= |a|
    ensures x !in a ==> forall u | 0 <= u < -k-1 :: a[u] < x
    ensures x !in a ==> forall u | -k-1 <= u < |a| :: a[u] > x
{
    // Recursive solution
    if a == [] { return -1; }
    var m := |a|/2;
    if a[m] == x { return m; }
    if a[m] > x
    {
        k := BinarySearchAnyEQ(a[..m],x);
    }
    else
    {
        k := BinarySearchAnyEQ(a[m+1..],x);
        if k < 0 { k := k-m-1; }
        else     { k := k+m+1; }
    }

    /*
    // Looping solution
    var p, q := 0, |a|;
    while p < q
        decreases q-p
        invariant 0 <= p <= q <= |a|
        invariant forall u | 0 <= u < p :: a[u] < x
        invariant forall u | q <= u < |a| :: a[u] > x
		
		//   a: |  < x  | ??? |  > x  |
		//       ^       ^     ^       ^
		//       0       p     q      |a|
    {
        var m := p+(q-p)/2;
        if a[m] == x { return m; }
        if a[m] < x  { p := m+1; }
        else         { q := m;   }
    }
    k := -p-1;
    */
}