// Author: Snorri Agnarsson, snorri@hi.is

// Use
//   dafny build -t:lib QuicksortLemmas.dfy --output:QuicksortLemmas.doo
// to build a library containing these methods and lemmas.

// But this may take a lot of computing time.

/*
C:\hivefur\TOL212M-25>wsl time cmd.exe /c \\dafny\\dafny build -t:lib --output:QuicksortLemmas.doo QuicksortLemmas.dfy

Dafny program verifier finished with 12 verified, 0 errors

real    1215m40.693s
user    0m0.000s
sys     0m0.000s
*/

method Swap( a: array<int>, i: int, p: int, q: int, j: int )
    modifies a
    requires 0 <= i <= p <= q < j <= a.Length
    ensures a[..p] == old(a[..p])
    ensures a[q+1..] == old(a[q+1..])
    ensures p < q ==> a[p+1..q] == old(a[p+1..q])
    ensures a[q] == old(a[p])
    ensures a[p] == old(a[q])
    ensures multiset(a[i..j]) == multiset(old(a[i..j]))
    ensures a[..i] == old(a[..i])
    ensures a[j..] == old(a[j..])
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    a[p], a[q] := a[q], a[p];
}

lemma SwappingLemma( a: seq<int>, b: seq<int>, i: int, r: int, s: int, j: int )
    requires |a| == |b|
    requires 0 <= i <= r <= s < j <= |a|
    requires a[..r] == b[..r]
    requires a[s+1..] == b[s+1..]
    requires a[r] == b[s]
    requires a[s] == b[r]
    requires r != s ==> a[r+1..s] == b[r+1..s]
    ensures multiset(a[i..j]) == multiset(b[i..j])

    ensures b[..r] == a[..r]
    ensures b[s+1..] == a[s+1..]
    ensures r < s ==> b[r+1..s] == a[r+1..s]
    ensures b[r] == a[s]
    ensures b[s] == a[r]
    ensures multiset(a[i..j]) == multiset(b[i..j])
    ensures b[..i] == a[..i]
    ensures b[j..] == a[j..]
{
    if r == s
    {
        calc ==
        {
            a;
            a[..r]+[a[r]]+a[r+1..];
            assert a[..r] == b[..r];
            assert [a[r]] == [b[r]];
            assert a[r+1..] == b[r+1..];
            b[..r]+[b[r]]+b[r+1..];
            b;
        }
        return;
    }
    calc ==
    {
        a[i..j];
        a[i..r]+[a[r]]+a[r+1..j];
        a[i..r]+[a[r]]+(a[r+1..s]+[a[s]]+a[s+1..j]);
        a[i..r]+[a[r]]+a[r+1..s]+[a[s]]+a[s+1..j];
        b[i..r]+[b[s]]+a[r+1..s]+[a[s]]+a[s+1..j];
        b[i..r]+[b[s]]+b[r+1..s]+[a[s]]+a[s+1..j];
        b[i..r]+[b[s]]+b[r+1..s]+[b[r]]+a[s+1..j];
    }
    SuperEqualImpliesSubEqual(a,b,s+1,j,|a|);
    LemmaConcatenateSeq(a,r+1,s,j);
    assert a[s+1..j] == b[s+1..j];
    calc ==
    {
        multiset(a[i..j]);
        calc ==
        {
            a[i..j];
            a[i..r]+a[r..j];
            b[i..r]+a[r..j];
            b[i..r]+[a[r]]+a[r+1..j];
            b[i..r]+[b[s]]+a[r+1..j];
            b[i..r]+[b[s]]+a[r+1..s]+a[s..j];
            b[i..r]+[b[s]]+b[r+1..s]+a[s..j];
            b[i..r]+[b[s]]+b[r+1..s]+[a[s]]+a[s+1..j];
            b[i..r]+[b[s]]+b[r+1..s]+[b[r]]+a[s+1..j];
            b[i..r]+[b[s]]+b[r+1..s]+[b[r]]+b[s+1..j];
        }
        assert a[i..j] == b[i..r]+[b[s]]+b[r+1..s]+[b[r]]+b[s+1..j];
        multiset(b[i..r]+[b[s]]+b[r+1..s]+[b[r]]+b[s+1..j]);
        multiset(b[i..r])+multiset{b[s]}+multiset(b[r+1..s]+[b[r]]+b[s+1..j]);
        multiset(b[i..r])+multiset{b[s]}+multiset(b[r+1..s])+multiset{b[r]}+multiset(b[s+1..j]);
        multiset(b[i..r])+multiset(b[r+1..s])+multiset{b[s]}+multiset{b[r]}+multiset(b[s+1..j]);
        multiset(b[i..r])+multiset(b[r+1..s])+multiset{b[r]}+multiset{b[s]}+multiset(b[s+1..j]);
        multiset(b[i..r])+multiset{b[r]}+multiset(b[r+1..s])+multiset{b[s]}+multiset(b[s+1..j]);
        assert b[i..r+1] == b[i..r]+[b[r]];
        multiset(b[i..r+1])+multiset(b[r+1..s])+multiset{b[s]}+multiset(b[s+1..j]);
        assert b[i..r+1]+b[r+1..s] == b[i..s];
        multiset(b[i..s])+multiset{b[s]}+multiset(b[s+1..j]);
        assert b[i..s+1] == b[i..s]+[b[s]];
        multiset(b[i..s+1])+multiset(b[s+1..j]);
        assert b[i..s+1]+b[s+1..j] == b[i..j];
        multiset(b[i..j]);
    }
}

lemma LemmaSinglePivotQuicksort
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
{
    assert forall u | i<=u<r :: sortedtwice[u] in multiset(sortedtwice[i..r]);
    LemmaConcatenateSeq(sortedonce,i,s,j);
    LemmaConcatenateSeq(sortedonce,i,r,j);
    LemmaConcatenateSeq(sortedtwice,i,s,j);
    LemmaConcatenateSeq(partitioned,i,r,j);

    calc ==
    {
        multiset(original[i..j]);
        multiset(partitioned[i..j]);
        multiset(partitioned[i..r]+partitioned[r..j]);
        multiset(partitioned[i..r])+multiset(partitioned[r..j]);
        multiset(sortedonce[i..r])+multiset(partitioned[r..j]);
        calc ==
        {
            partitioned[r..j];
            //{assert r <= j;}
            sortedonce[r..j];
        }
        multiset(sortedonce[i..r])+multiset(sortedonce[r..j]);
        multiset(sortedonce[i..j]);
        multiset(sortedonce[i..s]+sortedonce[s..j]);
        multiset(sortedonce[i..s])+multiset(sortedonce[s..j]);
        multiset(sortedtwice[i..s])+multiset(sortedonce[s..j]);
        multiset(sortedtwice[i..s])+multiset(sortedtwice[s..j]);
        multiset(sortedtwice[i..j]);
    }
    assert sortedonce[i..s] == sortedtwice[i..s];
    assert sortedonce[i..r] == sortedtwice[i..r];
    calc ==
    {
        multiset(partitioned[i..r]);
        multiset(sortedonce[i..r]);
        multiset(sortedtwice[i..r]);
    }

    assert forall u | i <= u < r :: sortedtwice[u] in multiset(sortedonce[i..r]);
    assert forall u | i <= u < r :: sortedtwice[u] in multiset(partitioned[i..r]);
    assert forall u | i <= u < r :: sortedtwice[u] <= p;
    assert forall u,v | i <= u < v < r ::
        sortedtwice[u] == sortedonce[u] <= sortedonce[v] == sortedtwice[v];
    calc ==
    {
        original[j..];
        partitioned[j..];
        sortedonce[j..];
        sortedtwice[j..];
    }

    assert forall u | s <= u < j :: sortedtwice[u] in multiset(sortedtwice[s..j]);
    assert sortedonce[r..] == partitioned[r..];

    assert sortedonce[r..] == partitioned[r..];
    assert forall u | r <= u < j :: sortedonce[u] == partitioned[u];
    assert sortedonce[r..j] == partitioned[r..j];

    assert sortedonce[s..j] == partitioned[s..j];
    assert forall u | s <= u < j :: sortedtwice[u] in multiset(partitioned[s..j]);
    assert forall u | s <= u < j :: sortedtwice[u] >= p;

    // | <=p | =p | >=p |
    // | x y |    |     |
    assert forall u,v | i <= u < v < r :: sortedtwice[u] <= sortedtwice[v];

    // | <=p | =p | >=p |
    // |  x  | y  |     |
    assert forall u | i <= u < r ::
            sortedtwice[u] in multiset(sortedtwice[i..r]) ==> 
            sortedtwice[u] in multiset(sortedonce[i..r]) ==>
            sortedtwice[u] in multiset(partitioned[i..r]) ==>
            sortedtwice[u] <= p;
    assert forall u,v | i <= u < r <= v < s :: sortedtwice[u] <= p == sortedtwice[v];
    assert forall u,v | i <= u < r <= v < s :: sortedtwice[u] <= p == sortedtwice[v];
    calc ==
    {
        original[..i];
        partitioned[..i];
        sortedonce[..i];
        {
            assert sortedonce[..s] == sortedtwice[..s];
            assert 0 <= i <= s;
            SuperEqualImpliesSubEqual(sortedonce,sortedtwice,0,i,s);
            assert sortedonce[..i] == sortedtwice[..i];
        }
        sortedtwice[..i];
    }
    assert sortedtwice[..i] == original[..i];
    assert multiset(sortedtwice[i..j]) == multiset(original[i..j]);
}

predicate less( x: int, y: int )
{
	x<y
}

lemma LemmaDualPivotQuicksort
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
{
    assert sortedonce[s..] == sortedtwice[s..];
    assert sortedonce[s..j] == sortedtwice[s..j];
    calc ==
    {
        multiset(sortedthrice[i..r]);
        calc ==
        {
            sortedthrice[i..r];
            sortedtwice[i..r];
        }
        multiset(sortedtwice[i..r]);
        calc ==
        {
            sortedtwice[i..r];
            sortedonce[i..r];
        }
        multiset(sortedonce[i..r]);
        multiset(partitioned[i..r]);
    }
    calc ==
    {
        multiset(sortedthrice[r+1..s]);
        calc ==
        {
            sortedthrice[..s];
            sortedtwice[..s];
        }
        multiset(sortedtwice[r+1..s]);
        multiset(sortedonce[r+1..s]);
        calc ==
        {
            sortedonce[r+1..s];
            partitioned[r+1..s];
        }
        multiset(partitioned[r+1..s]);
    }
    calc ==
    {
        multiset(sortedthrice[s+1..j]);
        multiset(sortedtwice[s+1..j]);
        calc ==
        {
            sortedtwice[s+1..j];
            sortedonce[s+1..j];
        }
        multiset(sortedonce[s+1..j]);
        calc ==
        {
            sortedonce[s+1..j];
            partitioned[s+1..j];
        }
        multiset(partitioned[s+1..j]);
    }
    calc ==
    {
        sortedthrice[j..];
        sortedtwice[j..];
        sortedonce[j..];
        partitioned[j..];
        original[j..];
    }
    calc ==
    {
        multiset(sortedthrice[i..j]);
        calc ==
        {
            sortedthrice[i..j];
            sortedthrice[i..s+1]+sortedthrice[s+1..j];
        }
        multiset(sortedthrice[i..s+1])+multiset(sortedthrice[s+1..j]);
        multiset(sortedtwice[i..s+1])+multiset(sortedtwice[s+1..j]);
        calc ==
        {
            sortedtwice[i..j];
            sortedtwice[i..s+1]+sortedtwice[s+1..j];
        }
        multiset(sortedtwice[i..j]);
        calc ==
        {
            sortedtwice[i..j];
            sortedtwice[i..r+1]+sortedtwice[r+1..j];
        }
        multiset(sortedtwice[i..r+1])+multiset(sortedtwice[r+1..j]);
        calc ==
        {
            sortedtwice[r+1..j];
            {
                LemmaConcatenateSeq(sortedtwice,r+1,s,j);
            }
            sortedtwice[r+1..s]+sortedtwice[s..j];
        }
        multiset(sortedtwice[i..r+1])+multiset(sortedtwice[r+1..s])+multiset(sortedtwice[s..j]);
        multiset(sortedtwice[i..r+1])+multiset(sortedonce[r+1..s])+multiset(sortedtwice[s..j]);
        multiset(sortedonce[i..r+1])+multiset(sortedonce[r+1..s])+multiset(sortedtwice[s..j]);
        multiset(sortedonce[i..r+1])+multiset(sortedonce[r+1..s])+multiset(sortedonce[s..j]);
        calc ==
        {
            sortedonce[i..r+1]+sortedonce[r+1..s];
            sortedonce[i..s];
        }
        multiset(sortedonce[i..s])+multiset(sortedonce[s..j]);
        calc ==
        {
            sortedonce[i..s]+sortedonce[s..j];
            { LemmaConcatenateSeq(sortedonce,i,s,j); }
            sortedonce[i..j];
        }
        multiset(sortedonce[i..j]);
        calc ==
        {
            sortedonce[i..r]+sortedonce[r..j];
            sortedonce[i..j];
        }
        multiset(sortedonce[i..r])+multiset(sortedonce[r..j]);
        multiset(partitioned[i..r])+multiset(sortedonce[r..j]);
        calc ==
        {
            sortedonce[r..j];
            partitioned[r..j];
        }
        multiset(partitioned[i..r])+multiset(partitioned[r..j]);
        calc ==
        {
            partitioned[i..r]+partitioned[r..j];
            partitioned[i..j];
        }
        multiset(partitioned[i..j]);
        multiset(original[i..j]);
    }

    assert sortedthrice[r] == sortedtwice[r] == sortedonce[r] == partitioned[r] == p;
    assert sortedthrice[s] == sortedtwice[s] == sortedonce[s] == partitioned[s] == q;

    // | x |p|   |q|   |
    assert i < r ==> sortedthrice[i] in sortedthrice[i..r];
    assert forall u | i <= u < r :: sortedthrice[u] in sortedthrice[i..r];
    assert forall u | i <= u < r :: sortedthrice[u] in multiset(partitioned[i..r]);
    assert forall u | i <= u < r :: sortedthrice[u] < p == sortedthrice[r];

    // | x y |p|   |q|   |
    assert forall u,v | i <= u < v < r :: sortedthrice[u] == sortedonce[u] <= sortedonce[v] == sortedthrice[v];

    // |   |p| x |q|   |
    assert forall u | r+1 <= u < s :: sortedthrice[u] in multiset(partitioned[r+1..s]);
    assert forall u | r+1 <= u < s :: p==sortedthrice[r] <= sortedthrice[u] <= q == sortedthrice[s];

    // |   |p| x y |q|   |
    assert forall u,v | r+1 <= u < v < s :: sortedthrice[u] == sortedtwice[u] <= sortedtwice[v] == sortedthrice[v];

    // |   |p|   |q| x |
    //  i   r     s     j
    assert forall u | r <= u < s :: p <= sortedthrice[u] <= q;
    assert forall u | s < u < j :: sortedthrice[u] in multiset(partitioned[s+1..j]);
    assert forall u | s < u < j :: q < sortedthrice[u];
    assert forall u | s < u < j :: q <= sortedthrice[u];

    // | x |p| y |q|   |
    assert forall u,v | i <= u < r < v < s :: sortedthrice[u] <= p == sortedthrice[r] <= sortedthrice[v];    

    // | x |p|   |q| y |
    assert forall u,v | i <= u < r < s < v < j :: sortedthrice[u] <= sortedthrice[v];    

    // |   |p| x |q| y |
    assert forall u,v | r <= u <= s <= v < j :: sortedthrice[u] <= sortedthrice[v];    

    calc ==
    {
        original[..i];
        sortedonce[..i];
        sortedtwice[..i];
        sortedthrice[..i];
    }
    assert
        (forall u,v {:trigger less(u,v)}| i <= u < v < j ::
            (
                ((i <= u < r && i <= v < r)) ||
                ((i <= u < r && v == r)) ||
                ((i <= u < r && r < v < s)) ||
                ((i <= u < r && v == s)) ||
                ((i <= u < r && s <= v < j)) ||
                ((u == r && r < v < s)) ||
                ((u == r && v == s)) ||
                ((u == r && s < v < j)) ||
                ((r < u < s && r < v < s)) ||
                ((r < u < s && v == s)) ||
                ((r < u < s && s < v < j)) ||
                ((u == s && s < v < j)) ||
                ((s < u < j && s < v < j))
            )
        );
    assert
        (forall u,v ::
            (
                ((i <= u < r && i <= v < r) ==> (sortedthrice[u] <= sortedthrice[v])) ||
                ((i <= u < r && v == r) ==> (sortedthrice[u] <= sortedthrice[v])) ||
                ((i <= u < r && r < v < s) ==> (sortedthrice[u] <= sortedthrice[v])) ||
                ((i <= u < r && v == s) ==> (sortedthrice[u] <= sortedthrice[v])) ||
                ((i <= u < r && s <= v < j) ==> (sortedthrice[u] <= sortedthrice[v])) ||
                ((u == r && r < v < s) ==> (sortedthrice[u] <= sortedthrice[v])) ||
                ((u == r && v == s) ==> (sortedthrice[u] <= sortedthrice[v])) ||
                ((u == r && s < v < j) ==> (sortedthrice[u] <= sortedthrice[v])) ||
                ((r < u < s && r < v < s) ==> (sortedthrice[u] <= sortedthrice[v])) ||
                ((r < u < s && v == s) ==> (sortedthrice[u] <= sortedthrice[v])) ||
                ((r < u < s && s < v < j) ==> (sortedthrice[u] <= sortedthrice[v])) ||
                ((u == s && s < v < j) ==> (sortedthrice[u] <= sortedthrice[v])) ||
                ((s < u < j && s < v < j) ==> (sortedthrice[u] <= sortedthrice[v]))
            )
        );
    assert
        (forall u,v | i <= u < v < j ::
            (
                ((i <= u < r && i <= v < r) && (sortedthrice[u] <= sortedthrice[v])) ||
                ((i <= u < r && v == r) && (sortedthrice[u] <= sortedthrice[v])) ||
                ((i <= u < r && r < v < s) && (sortedthrice[u] <= sortedthrice[v])) ||
                ((i <= u < r && v == s) && (sortedthrice[u] <= sortedthrice[v])) ||
                ((i <= u < r && s <= v < j) && (sortedthrice[u] <= sortedthrice[v])) ||
                ((u == r && r < v < s) && (sortedthrice[u] <= sortedthrice[v])) ||
                ((u == r && v == s) && (sortedthrice[u] <= sortedthrice[v])) ||
                ((u == r && s < v < j) && (sortedthrice[u] <= sortedthrice[v])) ||
                ((r < u < s && r < v < s) && (sortedthrice[u] <= sortedthrice[v])) ||
                ((r < u < s && v == s) && (sortedthrice[u] <= sortedthrice[v])) ||
                ((r < u < s && s < v < j) && (sortedthrice[u] <= sortedthrice[v])) ||
                ((u == s && s < v < j) && (sortedthrice[u] <= sortedthrice[v])) ||
                ((s < u < j && s < v < j) && (sortedthrice[u] <= sortedthrice[v]))
            ) &&
            (sortedthrice[u] <= sortedthrice[v])
        );
}

lemma LemmaConcatenateSeq( a: seq<int>, i: int, s: int, j: int )
    requires 0 <= i <= s <= j <= |a|
    ensures a[i..j] == a[i..s]+a[s..j]
{}

lemma SuperEqualImpliesSubEqual( a: seq<int>, b: seq<int>, i: int, s: int, j: int )
    decreases j-s
    requires |a| == |b|
    requires 0 <= i <= s <= j <= |a|
    requires a[i..j] == b[i..j]
    ensures a[i..s] == b[i..s]
    ensures a[s..j] == b[s..j]
{
    assert forall u | i <= u < s :: a[u] == b[u];
}