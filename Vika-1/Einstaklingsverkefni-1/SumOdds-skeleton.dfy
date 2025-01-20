// Author of question: Snorri Agnarsson
// Permalink of question: https://tinyurl.com/muvnbkjn

// Author of solution:    Andri Fannar Kristjánsson
// Permalink of solution: https://tio.run/##zVbbjhpHEH2fr6goLwvEA7aVF9ZrCTuKZCWKLa@ivEVqZmqgzUw37gsIbfZj8i3@sE1V9czABLBfvUJLX@p66lQ1parM4elpOoVFDGvrwFbwOaIP2po53BvrnIbFyijnvTUZyX1A16ham81QdB3C1s@n06DNIbo6L2wzbeLOLDefTJYN7Htbx6REfwtTkodflSEX8JvTPnz68q@56Oyol@e52PzTI4Q1AjlrlCn5CKDklOA@Nu/L0j/zG6wxWJOX1YHvrUtSpLLVNfbf1@SD7UXYU0WLnM/fO4it9z0uYatWeIKBzV000x8llBTqX2s0cLAR1mqHnMoOS9HeOrussYFtDOJvjX2iQB/e/yIZdW5@YrEVGnQqICjY9hgRBGwGNH1MMqZ9GzJv31IikXSeT15Ofp4QiJObF2Pz7PlITOoc8@Q@Ngx3Stf5ABRIWYKJzRKdz7MqmkLCazG7ASqJNgFG8pUBOPwctUNPmq/vYJY90JmuaHdHOzZsMq79jP5j7VE2nTGOByYggWWPCTvCWJF9qgWhtWPUlYB1lgg7MH@/yDJCtFHwgaXPorwQILEGC4fK8xHtyPYfNhASDjnwPReZlqqu7Z7rZkGV8pXYZ0rNgPikuaQSqCqgg@AO2qyoRjUZE0hp6@EdGNzR9V55UEtmVp@YTSZSxTnNIS6UnizG8v8W9pqait2VJTviaNBw1P4YVc4ot4e9sYTU2EhpuNHYCCxteYA1ZyqufawqXZCaNIHZaVPgWXzsM6FNXAsuMtdE5g2hCYWS8vbFp/WDlFt5j@6Y3UwCmt2e3s3kaNweOgzRGV4/HmmTbHH8Ap/DIjqvd1gf5GJQf0Hsku8ExiX@XRa/UIjrZk@kvm61q0jKkIjfINW27Jq2lfvd2u2RyS0oHm68nFymdld8P0hz9P@bb7GhSIH4bkYkUW2E3nYLexHlEce9Qa0igtQGje9Fzxu2crYh/lTS3U6v1iFP0h9TLWnMEK8M9U/XfDzl2EujDkmSLwv2N4TqY0eGjpD3QRHg4pBh2dGDo2Hess63K1ru1zztNfxwB6bjF@NOCZCOpkkkHdGoDaYJ0Q1NzV3niIRB1HpxYvKrOzL4qjN4vBnURI8u3eqxPmX6O5MGFdljJCjxItb8EhzLAikvPWmpJrl5oZ9O9HvMsq6jwN9eZVsP4XdFuZMuv04fLhiPxOvk4fMke4E8rP7VQQYPLXyz28dW7m3H@f6BHM4jKcM1gNMYSYYWZfppQHcO@d2jHsoGZWynyKCCzI2qA/uEi/Lepp8CaU7vNcW5t26Tt89kq7Oo65vTElXWcUYG/mkLC/P5lRfkTLRn7HAEj9rp9vT0Hw

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
  requires n >= 0
  decreases n
  // Not sure if we were allowed to add to the conditions
  // but after trying a lot of things I never was able to prove to
  // Dafny that SumOdds(n-1) == (n-1)*(n-1); without adding the ensures condition.
  ensures SumOdds(n) == n*n
{
  // Put a body here that suffices to convince
  // Dafny that the lemma is true.

  // Base case
  if n == 0
  {
    assert SumOdds(0) == 0;
    assert 0 == 0*0;
    return;
  }
  else
  {
    // Prove recursively
    ProveSumOdds(n-1);
    assert SumOdds(n) == SumOdds(n-1) + 2*n-1;
    assert SumOdds(n-1) == (n-1)*(n-1);
    assert SumOdds(n) == (n-1)*(n-1) + 2*n-1;
    assert SumOdds(n) == n*n;
  }
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

  // Start from 0
  var i := 0;
  s := 0;

  while i != n
    // Loop invariants to make sure the sum is correct
    invariant 0 <= i <= n
    invariant s == SumOdds(i)
    invariant s == i*i
  {
    // Increase i and calculate the sum
    i := i+1;
    s := s + 2*i-1;
  }

  return s;
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

  // Base case
  if n == 0 {return 0;}

  // Call the function recursively
  s := ComputeSumOddsRecursive(n-1);

  // Add the current term
  s := s + 2*n-1;
  return s;
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