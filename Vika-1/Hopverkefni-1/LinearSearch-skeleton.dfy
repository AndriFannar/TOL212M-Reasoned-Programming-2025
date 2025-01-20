// Author of question: Snorri Agnarsson
// Permalink of question: https://tinyurl.com/mssdpfvr

// Author of solution:    Andri Fannar Kristjánsson
// Permalink of solution: https://tio.run/##7Vbbjts2EH33V0zRh@yiXjv76uwFixYLBA3QoEGRhyAFaGls0aJI7ZDyBfF@TP@g/5AP286Qkiwl26Dtcw2b5mUuhzNnRsrVyh6enuZzuGtC4QjcCh4a9EE7u4B31hFpuFtbRd47O2G5t0iVMtqWY9EihNov5vOg7aEhM8tcNa@8z@vVliaTkX3vTJOU@HNnc/Zwryy7gJ9J@7D5/Id91tlJbzabRZu/eYRQILCzStlctgByuRK80RYVveNfVlz4Eg0GZ2f56iBCjpIo69Xa4LeFg@vlxNeKJzPZ/4Wgaf3vcAm1WvNCuxk1dv59BJFAvi/QwsE1UKgtyiW2mEetmtzSYAV1E6KfAvsrAn9l/VO8S2d@KmJrtEgqICio@@jw5cUMaP7aZEz7FupkUiGHPod0v18xa8jrLZ6BWoDHhyttw80U9IJVwxQ27f8@/sM5EIaGrIezMu6cTyYA7IGVj5IIHm9vb7t5OpPP71@Pp8OXcdRx3MhwVEexS/jQaELPAlfXfM7DRgY5BkDrGzmM@yVc8dnxyJPra7i4HJyX8J3s8P4NqA/lRxHY/835ypEyBgiO0SJFq4sF69FHERvrXT@nF@E8o/gp3fct54VTvSZVQcB9gAJJMs05UiFluI1olmEdfJu7xmbChFk6e23H22Ccqz0otmRdAIbidpgn2SU7pJRlFvSFa0wOSxS25tNIFR2SJBscaEemy6UizVtHSTBR5w37ZEMsPGtJ8HolysAFU6Fl6DrRVhGpQ@L7Epn9WYFZKc4Tl1K2pDQclR52OhRguPK9VLlBu@b1JShJ9LUQgMP9UmaXEjWO/87ZF0FulMwxcl1VmGuuCiOx1KtWk@eSBODMLSRzr3jxmFz/KJDYd8G1gRRRt7cAJUWU4x427ItDxJxURoKzhzOvbYYDAk65ODlogidektHmTOAsmEMXjKXyIuLxXKhkeMH41Ac23hNzAHIzQsnx/RYySd4J3fTr7HU82HJgUpzl1CgfepuEldtG6gi2MZgvO4biNjEV59wezhPMWLSShVeTxy9bjfDlP3eZ/5vBP28Gp2ofV3RrKlb8vy32PuuglkyQruLfM9qgKHIxUpONu9Wg6sWbMIp5n5U7RbmfyoMKWmbk6DPSdestUR4ugEnPy10hT9kSbjjdkYU5ZoRcOhLui3YvBmCrSCsmDmMJ6FP0Rp0ouIiJ9LoIArDse@WwYJSo4jOtqvN03xh@ipoo1l7hhe85kBnVxJrhntND6snA@S9/uDzxITHwxKRPnZPYV0NBrlkXMX6plaDKir5Mh52166ParmOvC@MulfCsRmzvvJ2qVeaxfNsslCkL7WbqPdad/PtR4IaNfNBcO@PJwj33GXWgz38KUHMoy02z6N8B4vtDenPgcAUOyn74@tC/HtTQfzaTx6envwA

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

  // If all elements in the array have been checked, return -1
  // Works with lists of length 1 as i == j => 0 == 1 so -1 won't be returned immediately
  if i == j
  {
    k := -1;
  }
  // Checks whether the element at index j-1 is equal to x (since i <= k < j, we can't check j directly in the base case)
  else if a[j-1] == x
  {
    k := j-1;
  }
  // If the element at index j-1 is not equal to x, call the function recursively with the last element removed
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

  // We start at the end of the array and move backwards, per method description
  k := j - 1;

  while k >= i
    decreases k - i
    // Invariant states that all elements to the right of k are not equal to x, as they have been checked
    // Fulfills the method's ensures clause
    invariant forall r :: k+1 <= r < j ==> a[r] != x
  {
    // Loop through and check each element in the array, returning if it is equal to x
    if a[k] == x
    {
      return;
    }

    k := k - 1;
  }

  // If no element is equal to x, return -1
  k := -1;
  return;

  // Fastayrðing lykkju:
  //    a: | ??? | allt !=x |
  //        i     p          j
}