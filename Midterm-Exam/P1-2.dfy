method searchRecursive( s: seq<int>, a: int, b: int ) returns( k: int )
    requires forall i,j | 0<=i<j<|s| :: s[i]<=s[j] 
    ensures k==-1 ==> forall z | z in s :: z<a || z>b
    ensures k!=-1 ==> 0<=k<|s| && a<=s[k]<=b
{ 
    if s==[] { return -1; }
    var m:=|s|/2;
    if a<=s[m]<=b {return m;}
    // Öll eftirfarandi assert eru ónauðsynleg fyrir mannlega lesendur
    // en eru nauðsynlegar fyrir Dafny.
    // All the following asserts are not necessary for human readers
    // but are necessary for Dafny.
    if s[m]<a
    {
        assert forall z | z in s[..m+1] :: z<a;
        k:=searchRecursive(s[m+1..],a,b);
        assert k==-1 ==> forall z | z in s[m+1..] :: z<a || z>b;
        assert s==s[..m+1]+s[m+1..];
        if k!=-1 {k:=k+m+1;}
    }
    else // s[m]>b
    {
        k:=searchRecursive(s[..m],a,b);
        assert forall z | z in s[m..] :: z>b;
        assert s==s[..m]+s[m..];
    }
}

method searchLoop( s: seq<int>, a: int, b: int ) returns( k: int )
    requires forall i,j | 0<=i<j<|s| :: s[i]<=s[j] 
    ensures k==-1 ==> forall z | z in s :: z<a || z>b
    ensures k!=-1 ==> 0<=k<|s| && a<=s[k]<=b
{
    var p,q := 0,|s|;
    while p<q
        invariant 0 <= p <= q <= |s| 
        invariant forall i | 0<=i<p :: s[i]<a
        invariant forall i | q<=i<|s| :: s[i]>b 
    {
        var m := p+(q-p)/2;
        if a<=s[m]<=b { return m; }
        if s[m]<a { p := m+1; }
        else      { q := m;   }
    }
    return -1;
}