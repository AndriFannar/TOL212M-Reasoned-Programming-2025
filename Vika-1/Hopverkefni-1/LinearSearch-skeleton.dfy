// Author of question: Snorri Agnarsson
// Permalink of question: https://tinyurl.com/mssdpfvr

// Author of solution:    Andri Fannar Kristjánsson
// Permalink of solution: ...

// Use the command
//   dafny LinearSearch-skeleton.dfy
// or
//   compile LinearSearch-skeleton.dfy
// to compile the file.
// Or use the web page tio.run/#dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

method SearchRecursive( a: seq<int>, i: int, j: int, x: int ) returns (k: int)

  // a: | ... | ??? | ... |
  //     ^     ^     ^     ^
  //     0     i     j    |a|

  requires 0 <= i <= j <= |a|
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
{
  // Put program text here so that Dafny
  // accepts this function.
  // In this function loops are not allowed
  // but recursion should be used, and it
  // is not allowed to call the function
  // SearchLoop below.
  if i == j
  {
    k := -1;
  }
  else if a[j-1] == x
  {
    k := j-1;
  }
  else
  {
    k := SearchRecursive(a, i, j-1, x);
  }

  return;
}

method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
  requires 0 <= i <= j <= |a|
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
{
  // Put program text here so that Dafny
  // accepts this function.
  // In this function recursion is not allowed
  // and it is not allowed to call the function
  // SearchRecursive above.

  k := j - 1;

  while k >= i
    decreases k - i
    invariant forall r :: k+1 <= r < j ==> a[r] != x
  {
    if a[k] == x
    {
      return;
    }

    k := k - 1;
  }

  k := -1;
  return;

  // Fastayrðing lykkju:
  //    a: | ??? | allt !=x |
  //        i     p          j
}