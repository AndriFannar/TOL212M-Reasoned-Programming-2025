include "BST.dfy"

// Q2
// Write a recursive binary search function in Dafny that
// searches in a section of an integer sequence that is sorted in
// descending order for the rightmost position that contains a
// number greater than 2025. If no such position exists, return -1.
method BinarySearchQ2( a: seq<int>, i: int, j: int ) returns ( k: int )
  decreases j-i
  requires 0 <= i <= j <= |a|
  requires forall p,q | i <= p <= q < j :: a[p] >= a[q]
  ensures k == -1 ==> forall p | i <= p < j :: a[p] <= 2025
  ensures k != -1 ==> (i <= k < j) &&
                      (forall p | k < p < j :: a[p] <= 2025) &&
                      (a[k] > 2025)
{
  if (i == j) { return -1; }
  var m := i+(j-i)/2;
  if (a[m] > 2025)
  {
    k := BinarySearchQ2(a, m+1, j);
    if (k == -1) { k := m; }
  }
  else { k := BinarySearchQ2(a, i, m); }
}


// Q4
// Assume a Dafny function exists with the following descripion:
// 
//  method MiddlePartition( a: array<int>, i: int, j: int )
//      returns( p: int )
//    modifies a
//    requires 0 <= i < j <= a.Length
//    ensures i <= p < j
//    ensures forall r | i <= r < p :: a[r] <= a[p]
//    ensures forall r | p < r < j :: a[r] >= a[p]
//    ensures a[p] == old(a[(i+j)/2])
//    ensures multiset(a[i..j]) == old(multiset(a[i..j]))
//    ensures a[..i] == old(a[..i])
//    ensures a[j..] == old(a[j..])
//
// Write a Quicksort function that uses this function as a helper
// function. Do not implement the MiddlePartition function here.
/*method QuickSortQ4( a: array<int>, i: int, j: int )
  modifies a
  decreases j-i
  requires 0 <= i <= j <= a.Length
  ensures forall p,q | i <= p <= q < j :: a[p] <= a[q]
  ensures multiset(a[i..j]) == old(multiset(a[i..j]))
  ensures a[..i] == old(a[..i])
  ensures a[j..] == old(a[j..])
{
  if ( i==j /* j-i/2 would be better */ ) { return; }
  var p := MiddlePartition(a, i, j);
  QuickSortQ4(a, i, p);
  QuickSortQ4(a, p, i); /* Should be QuickSortQ4(a, p+1, j); */
}*/


// Q7
// Assume the definition
//    datatype BST = BSTEmpty | BSTNode(BST, int, BST)
// as in our file BST.dfy. Also assume the function IsTreePath,
// TreeSeq, PreSeq, MidSeq, PostSeq, PreSeqIncluding, etc.
// Write a function that searches in a binary search tree and
// returns a reference to the leftmost node that contains a
// positive number (a number greater than zero), or returns
// BSTEmpty if such a node does not exist in the tree.
// Remember to write a full description with requires/ensures
// and to write an invariant for your loops if you use loops.
method SearchBSTQ7( t: BST ) returns ( p: BST, ghost rp: seq<dir> )
  requires TreeIsSorted(t)
  ensures p == BSTEmpty ==> forall x | x in TreeSeq(t) :: x <= 0
  ensures p != BSTEmpty ==>
            (IsTreePath(t, rp)) &&
            (p == Subtree(t, rp)) &&
            (forall x | x in PreSeqExcluding(t, rp) :: x <= 0) &&
            (forall x | x in PostSeqIncluding(t, rp) :: x > 0)
{
  RecursionSearchLemma(); // Not in the test.
  if (t == BSTEmpty) { return BSTEmpty, []; }
  if (RootValue(t) <= 0)
  {
    p, rp := SearchBSTQ7(Right(t));
    if (p != BSTEmpty) { rp := [1] + rp; }
  }
  else
  {
    p, rp := SearchBSTQ7(Left(t));
    if (p == BSTEmpty) { return t, []; }
    else               { rp := [0] + rp; }
  }
}


// Q9
// Write a function in Dafny that takes one argument, a binary
// search tree t, and returns true if a negative number exists in
// the tree and returns false otherwise. You may use a loop or
// recursion, given that the reasoning is correct (i.e. correct
// requires, ensures and invariant.)
method SearchBSTQ9( t: BST ) returns( b: bool )
  requires TreeIsSorted(t)
  ensures b <==> exists x | x in TreeSeq(t) :: x < 0
{
  if ( t == BSTEmpty )    { return false; }
  if ( RootValue(t) < 0 ) { return true;  }
  else                    
  { 
    b := SearchBSTQ9(Left(t)); 
    return b;
  }
}

// 11
// Program the body of the function below. Use recursion and
// not a loop.
//
//  method Minimum( f: real->real
//                , a: real
//                , b: real
//                , c: real
//                , eps: real )
//      returns ( d: real, e: real )
//    decreases ((c-a)/eps).Floor
//    requires a < c
//    requires b == (a+c)/2.0
//    requires eps > 0.0
//    requires f(b) <= f(a)
//    requires f(b) <= f(c)
//    ensures a <= d < e <= c
//    ensures e-d < eps
//    ensures f((d+e)/2.0) <= f(d)
//    ensures f((d+e)/2.0) <= f(e)
//
// Hint: The following lemma can be proven in Dafny. You do not
// need to call it.
//
// lemma BisectionTermination( x: real, y: real, eps: real )
//    requires eps > 0.0
//    requires x >= eps > 0.0
//    requires y == x/2.0
//    ensures (x/eps).Floor > (y/eps).Floor

  method Minimum( f: real->real
                , a: real
                , b: real
                , c: real
                , eps: real )
      returns ( d: real, e: real )
    decreases ((c-a)/eps).Floor
    requires a < c
    requires b == (a+c)/2.0
    requires eps > 0.0
    requires f(b) <= f(a)
    requires f(b) <= f(c)
    ensures a <= d < e <= c
    ensures e-d < eps
    ensures f((d+e)/2.0) <= f(d)
    ensures f((d+e)/2.0) <= f(e)
{
  if (c-a < eps) { return a, c; }
  if ( f((a+b)/2.0) < f((b+c)/2.0)) /* This condition does not ensure that f((a+b)/2.0) <= f(a) and f((a+b)/2.0 <= f(b)) */
  {
    d, e := Minimum(f, a, (a+b)/2.0, b, eps);
  }
  else
  {
    d, e := Minimum(f, b, (b+c)/2.0, c, eps);
  }
  // We need to handle three cases here. You don't ahndle the case when
  // f(b) continues to be <= f(a) and f(c) for new values of a and c,
  // i.e. a := (a+b)/2.0 and c := (b+c)/2.0.
  // In addition you don't need to call the function recursively twice
  // as it's faster to determine beforehand what call to use.
  // Also, it's not ensured that the preconditions for all calls are fulfilled.
}