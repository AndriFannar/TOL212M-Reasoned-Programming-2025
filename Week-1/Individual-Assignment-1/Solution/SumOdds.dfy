// Author of question: Snorri Agnarsson
// Permalink of question: https://tinyurl.com/muvnbkjn

// Author of solution:    ...
// Permalink of solution: ...

// Use the command
//   dafny SumOdds-skeleton.dfy
// or
//   compile compile SumOdds-skeleton.dfy
// to compile the file.
// Or use the web page https://tio.run/#dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

// Compute 1+3+5+...+(2*n-1),
// i.e. the sum of the first n odd numbers.
function SumOdds( n: int ): int
    requires n >= 0
{
    if n == 0 then
        0
    else
        SumOdds(n-1) + 2*n-1
}

// We want to prove that
// 1+3+5+...+(2*n-1) == n^2

lemma ProveSumOdds( n: int )
    // Put requires and ensures clauses here that
    // ensure that the formula to prove is true.
    requires n >= 0
    ensures SumOdds(n) == n*n
{
    // Put a body here that suffices to convince
    // Dafny that the lemma is true.
}

method ComputeSumOddsLoop( n: int ) returns (s: int)
    requires n >= 0
    ensures s == SumOdds(n)
    ensures s == n*n
{
    // Put a body here that computes the sum
    // in a loop where you add all the terms
    // in 1+3+5+...+(2*n-1) from left to right.
    // Recursion is not allowed and you may
    // not call ComputeSumOddsRecursive.
    s := 0;
    var i := 0;
    while i < n 
        invariant 0 <= i <= n 
        invariant s == SumOdds(i) 
        invariant s == i*i
    {
        i := i+1;
        s := s+i+i-1;
    }
}

method ComputeSumOddsRecursive( n: int ) returns (s: int)
    requires n >= 0
    ensures s == SumOdds(n)
    ensures s == n*n
{
    // Put a body here that computes the sum
    // recursively from left to right.
    // Looping is not allowed and you may not
    // call ComputeSumOddsLoop.
    if n == 0 { return 0; }
    s := ComputeSumOddsRecursive(n-1);
    s := s+n+n-1;
}

// If SumOdds is correct then this lemma will work.
lemma SumOddsAll()
    ensures forall n | n >= 0 :: SumOdds(n) == n*n
{
    forall n | n >= 0 
    {
        ProveSumOdds(n);
    }
}