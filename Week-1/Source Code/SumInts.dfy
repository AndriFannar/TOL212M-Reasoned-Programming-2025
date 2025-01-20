// For a given n >= 0, compute 1+2+...+n
function SumIntsFun( n: int ): int
  requires n >= 0
  decreases n
  ensures SumIntsFun(n) == n*(n+1)/2
{
  if n==0 then
    0
  else
    SumIntsFun(n-1)+n
}

// Prove, for a given n >= 0, that
// 1+2+3+...+n == n*(n+1)/2
lemma SumIntsLemma( n: int )
  requires n >= 0
  decreases n
  ensures SumIntsFun(n) == n*(n+1)/2
{
  // In fact this body is unnecessary,
  // Dafny will (probably) not need it
  // to prove the lemma, but bodies
  // like this are often needed.
  if n == 0 { return; }
  SumIntsLemma(n-1);  
}

// Prove, for all n >= 0, that
// 1+2+3+...+n == n*(n+1)/2
lemma SumIntsAll()
  ensures forall n | n >= 0 :: SumIntsFun(n) == n*(n+1)/2
{
  // This body also is unnecessary,
  // Dafny will (probably) not need it
  // to prove the lemma, but it shows
  // a type of body that is sometimes
  // needed in a lemma proving a forall.
  forall n | n >= 0
  {
    SumIntsLemma(n);
  }
}

// For a given n >= 0, compute
// 1+2+3+...+n and prove that
// 1+2+3+...+n == n*(n+1)/2
method SumIntsRecursive( n: int ) returns ( s: int )
  requires n >= 0
  ensures s == n*(n+1)/2
  ensures s == SumIntsFun(n)
{
  if n == 0 { return 0; }
  s := SumIntsRecursive(n-1);
  s := s+n;
}

// For a given n >= 0, compute
// 1+2+3+...+n tail-recursively and prove that
// 1+2+3+...+n == n*(n+1)/2
method SumIntsTailRecursive( n: int ) returns ( s: int )
  requires n >= 0
  ensures s == n*(n+1)/2
  ensures s == SumIntsFun(n)
{
  s := SumIntsTailRecursiveHelp(n,0,0);
}

// Compute (i+1)+(i+2)+...+(n-1)+n tail-recursively
method SumIntsTailRecursiveHelp( n: int, i: int, s: int ) returns ( r: int )
  requires 0 <= i <= n
  requires s == i*(i+1)/2
  requires s == SumIntsFun(i)
  ensures r == n*(n+1)/2
  ensures r == SumIntsFun(n)
  decreases n-i
{
  if i == n { return s; }
  r := SumIntsTailRecursiveHelp(n,i+1,s+i+1);
}

// For a given n >= 0, compute
// 1+2+3+...+n and prove that
// 1+2+3+...+n == n*(n+1)/2
method SumIntsLoop( n: int ) returns ( s: int )
  requires n >= 0
  ensures s == n*(n+1)/2
  ensures s == SumIntsFun(n)
{
  s := 0;
  var k := 0;
  while k != n
    decreases n-k
    invariant 0 <= k <= n
    invariant s == k*(k+1)/2
    invariant s == SumIntsFun(k)
  {
    k := k+1;
    s := s+k;
  }
}

method Main()
{
  // This call to the lemma is (probably)
  // not necessary.
  SumIntsAll();
  
  assert forall n | n >= 0 :: SumIntsFun(n) == n*(n+1)/2;
  print "Success!";
}
