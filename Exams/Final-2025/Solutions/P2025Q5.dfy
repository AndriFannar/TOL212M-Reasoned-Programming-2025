method MiddlePartition( a: array<int>, i: int, j: int ) returns( p: int )
    modifies a
    requires 0 <= i < j <= a.Length
    ensures i <= p < j
    ensures forall r | i <= r < p :: a[r] <= a[p]
    ensures forall r | p < r < j :: a[r] >= a[p]
    ensures a[p] == old(a[(i+j)/2])
    ensures multiset(a[i..j]) == old(multiset(a[i..j]))
    ensures a[..i] == old(a[..i])
    ensures a[j..] == old(a[j..])
{
    var mid := (i+j)/2;
    assert i <= mid < j;
    assert 0 <= mid < a.Length;
    var pivot := a[mid];
    a[i], a[mid] := a[mid], a[i];
    assert multiset(a[i..j]) == old(multiset(a[i..j]));
    var r, s := i+1, i+1;
    while s < j
        decreases j-s
        invariant i < r <= s <= j
        invariant a[i] == pivot == old(a[(i+j)/2])
        invariant forall t | i < t < r :: a[t] < pivot
        invariant forall t | r <= t < s :: a[t] >= pivot
        invariant a[..i] == old(a[..i])
        invariant a[j..] == old(a[j..])
        invariant multiset(a[i..j]) == old(multiset(a[i..j]))
    {
        // |x| <x | >=x | ??? |
        //  i      r     s     j
        if a[s] < pivot
        {
            ghost var oldm := multiset(a[i..j]);
            assert oldm == old(multiset(a[i..j]));
            if r != s { a[r], a[s] := a[s], a[r]; }
            assert  multiset(a[i..j]) == oldm;
            assert multiset(a[i..j]) == oldm == old(multiset(a[i..j]));
            r := r+1;
        }
        s := s+1;
    }
    // |x| <x | >=x |
    //  i      r     j
    r := r-1;
    assert i <= r < j;
    // |x| <x | >=x |
    //  i    r       j
    a[i], a[r] := a[r], pivot;
    return r;
}