// Author: Snorri Agnarsson.

method Swap( a: array<int>, i: int, p: int, q: int, j: int )
    modifies a
    requires 0 <= i <= p <= q < j <= a.Length
    ensures a[..p] == old(a[..p])
    ensures a[q+1..] == old(a[q+1..])
    ensures p < q ==> a[p+1..q] == old(a[p+1..q])
    ensures a[q] == old(a[p])
    ensures a[p] == old(a[q])
    ensures multiset(a[i..j]) == multiset(old(a[i..j]))
{
    a[p], a[q] := a[q], a[p];
}

lemma {:axiom} LemmaSinglePivotQuicksort
        ( original: seq<int>
        , partitioned: seq<int>
        , sortedonce: seq<int>
        , sortedtwice: seq<int>
        , i: int
        , r: int
        , s: int
        , j: int
        , p: int
        )
    requires |original| == |partitioned| == |sortedonce| == |sortedtwice|
    requires 0 <= i <= r <= s <= j <= |original|
    requires original[..i] == partitioned[..i]
    requires original[j..] == partitioned[j..]
    requires forall u | i <= u < r :: partitioned[u] <= p
    requires forall u | r <= u < s :: sortedtwice[u] == p
    requires forall u | s <= u < j :: partitioned[u] >= p
    requires multiset(original[i..j]) == multiset(partitioned[i..j])
    requires partitioned[..i] == sortedonce[..i]
    requires partitioned[r..] == sortedonce[r..]
    requires multiset(partitioned[i..r]) == multiset(sortedonce[i..r])
    requires forall u,v | i <= u < v < r :: sortedonce[u] <= sortedonce[v]
    requires sortedonce[..s] == sortedtwice[..s]
    requires sortedonce[j..] == sortedtwice[j..]
    requires multiset(sortedonce[s..j]) == multiset(sortedtwice[s..j])
    requires forall u,v | s <= u < v < j :: sortedtwice[u] <= sortedtwice[v]
    ensures forall u,v | i <= u < v < j :: sortedtwice[u] <= sortedtwice[v]
    ensures sortedtwice[..i] == original[..i]
    ensures sortedtwice[j..] == original[j..]
    ensures multiset(sortedtwice[i..j]) == multiset(original[i..j])

lemma {:axiom} LemmaDualPivotQuicksort
    ( original: seq<int>
    , partitioned: seq<int>
    , sortedonce: seq<int>
    , sortedtwice: seq<int>
    , sortedthrice: seq<int>
    , i: int
    , r: int
    , s: int
    , j: int
    , p: int
    , q: int
    )
    // Size and index preconditions:
    requires |original| == |partitioned| == |sortedonce| == |sortedtwice| == |sortedthrice|
    requires 0 <= i <= r < s < j <= |original|
    requires p <= q
    // Contents of partitioned:
    requires original[..i] == partitioned[..i]
    requires original[j..] == partitioned[j..]
    requires multiset(original[i..j]) == multiset(partitioned[i..j])
    requires partitioned[r] == p
    requires partitioned[s] == q
    requires forall u | i <= u < r :: partitioned[u] < p
    requires forall u | r < u < s :: p <= partitioned[u] <= q
    requires forall u | s < u < j :: partitioned[u] > q
    // Contents of sortedonce:
    requires partitioned[..i] == sortedonce[..i]
    requires partitioned[r..] == sortedonce[r..]
    requires multiset(partitioned[i..r]) == multiset(sortedonce[i..r])
    requires forall u,v | i <= u < v < r :: sortedonce[u] <= sortedonce[v]
    // Contents of sortedtwice:
    requires sortedonce[..r+1] == sortedtwice[..r+1]
    requires sortedonce[s..] == sortedtwice[s..]
    requires multiset(sortedonce[r+1..s]) == multiset(sortedtwice[r+1..s])
    requires forall u,v | r < u < v < s :: sortedtwice[u] <= sortedtwice[v]
    // Contents of sortedthrice:
    requires sortedtwice[..s+1] == sortedthrice[..s+1]
    requires sortedtwice[j..] == sortedthrice[j..]
    requires multiset(sortedtwice[s+1..j]) == multiset(sortedthrice[s+1..j])
    requires forall u,v | s < u < v < j :: sortedthrice[u] <= sortedthrice[v]

    // Postconditions:
    ensures forall u,v | i <= u < v < j :: sortedthrice[u] <= sortedthrice[v]
    ensures sortedthrice[..i] == original[..i]
    ensures sortedthrice[j..] == original[j..]
    ensures multiset(sortedthrice[i..j]) == multiset(original[i..j])
