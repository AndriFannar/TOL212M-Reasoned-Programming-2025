include "BST.dfy"
// Q1
// Write a function in Dafny that uses Binary Search to find the
// leftmost position in an ascending integer array a that contains
// a zero. If no such position exists then return -1.

method BinarySearchQ1 ( a: seq<int> ) returns ( k: int )
  requires forall p,q | 0 <= p < q < |a| :: a[p] <= a[q]
  ensures -1 <= k < |a|
  ensures k == -1 ==> forall z | z in a :: z != 0
  ensures k >= -1 ==>  forall p | 0 <= p < k :: a[p] < 0
{
  // VERIFIED
  var p, q := 0, |a|;
  while ( p < q )
    decreases q-p
    invariant 0 <= p <= q <= |a|
    invariant forall s | 0 <= s < p :: a[s] < 0
    invariant forall s | q <= s < |a| :: a[s] >= 0
  {
    var m := p+(q-p)/2;
    if ( a[m] < 0 ) { p := m+1; }
    else { q := m; }
  }
  if ( p == |a| ) { return -1; }
  if ( a[p] != 0 ) { return -1; }
  k := p;
}

// Q2
// Write a recursive Binary Search method in Dafny that searches
// in a section of an integer array that is in descending order for
// the rightmost position that contains a positive number. If no
// such position exists return -1

method BinarySearchQ2 ( a: seq<int>, i: int, j: int ) returns ( k: int )
  decreases j-i
  requires 0 <= i <= j <= |a|
  requires forall p,q | 0 <= p < q < |a| :: a[p] >= a[q]
  ensures k == -1 ==> forall p | i <= p < j :: a[p] <= 0
  ensures k != -1 ==> i <= k < j &&
                      a[k] > 0 &&
                      forall p | k < p < j :: a[p] <= 0
{
  // VERIFIED
  if ( i == j ) { return -1; }
  var m := i+(j-i)/2;
  if ( a[m] > 0 )
  {
    k := BinarySearchQ2(a, m+1, j);
    if ( k == -1 ) { k := m; }
  }
  else
  {
    k := BinarySearchQ2(a, i, m);
  }
}

// Q4
// Assume a Dafny function with the following description:
//
//	method Partition ( a: multiset<int> )
//			returns ( b: multiset<int>, c: seq<int>, d: multiset<int> )
//		requires |a| > 0;
//		ensures exists p | p in a ::
//				(forall z | z in b :: z <= p ) &&
//				(forall z | z in c :: z == p ) &&
//				(forall z | z in d :: z >= p )
//		ensures a == b + multiset(c) + d
//		ensures |c| > 0
//
// Write a Quicksort function that uses this function as a helper
// function to transform a multiset into a sorted sequence of the
// same values. Do not program the Partition function here.

method QuicksortQ4 ( a: multiset<int> )
  returns ( s: seq<int> )
  decreases |a|
  ensures forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
  ensures multiset(s) == a
{
  // VERIFIED (With asserts provided in solutions)
  if ( a == multiset{} ) { return []; }
  var b, c, d := Partition(a);
  var b' := QuicksortQ4(b);
  var d' := QuicksortQ4(d);
  s := b' + c + d';
}

// Q5
// Program the Partition function described above. Remember
// that all loops need an invariant.

method Partition ( a: multiset<int> )
  returns ( b: multiset<int>, c: seq<int>, d: multiset<int> )
  requires |a| > 0
  ensures exists p | p in a ::
            (forall z | z in b :: z <= p ) &&
            (forall z | z in c :: z == p ) &&
            (forall z | z in d :: z >= p )
  ensures a == b + multiset(c) + d
  ensures |c| > 0
{
  // VERIFIED
  var x :| x in a;
  var a' := a - multiset{x};
  if ( a' == multiset{} ) { return multiset{}, [x], multiset{}; }
  b, c, d := Partition(a');
  var p :| p in c;
  if ( x < p ) { b := b + multiset{x}; }
  else { d := d + multiset{x}; }
}

// Q6
// Program the following Dafny function:
//
//	method Quickselect( a: multiset<int>, k: int )
//			returns( b: multiset<int>, c: seq<int>, d: multiset<int> )
//		requires 0 <= k < |a|
//		ensures a == b + multiset(c) + d
//		ensures |b| <= k < |b|+|c|
//		ensures forall p, q | p in c && q in c :: p == q
//		ensures forall p, q | p in b && q in c :: ð <= q
//		ensures forall p, q | p in d && q in c :: p >= q
//
// You may use the Partition function as a helper function.

method Quickselect( a: multiset<int>, k: int )
  returns( b: multiset<int>, c: seq<int>, d: multiset<int> )
  decreases |a|
  requires 0 <= k < |a|
  ensures a == b + multiset(c) + d
  ensures |b| <= k < |b|+|c|
  ensures forall p, q | p in c && q in c :: p == q
  ensures forall p, q | p in b && q in c :: p <= q
  ensures forall p, q | p in d && q in c :: p >= q
{
  // VERIFIED (With provided asserts in solutions)
  b, c, d := Partition(a);
  if ( |b| <= k < |b| + |c| )
  {
    return;
  }
  if ( |b| > k )
  {
    var b', c', d' := Quickselect(b, k);
    d := d + multiset(c) + d';
    b := b';
    c := c';
  }
  else
  {
    var b', c', d' := Quickselect(d, k-|b|-|c|);
    b := b' + multiset(c) + b;
    c := c';
    d := d';
  }
}

// Q7
// Assume the definition
//		datatype BST = BSTEmpty | BSTNode(BST, int, BST)
// as in our file BST.dfy. Also assume the functions IsTreePath
// TreeSeq, PreSeq, MidSeq, PostSeq, PreSeqIncluding, etc.
// Write a function that searches in a binary search tree and
// returns a reference to the rightmost node that contains a
// negative number (a number less than zero), or returns
// BSTEmpty if such a node does not exist in the tree.
// Remember to write a full description with requires/ensures
// and to write an invariant for your loops if you use loops.

method SearchBSTQ7 ( t: BST ) returns ( r: BST, ghost p: seq<dir> )
  decreases t
  requires TreeIsSorted(t)
  ensures r == BSTEmpty ==> forall x | x in TreeSeq(t) :: x >= 0
  ensures r != BSTEmpty ==>
            IsTreePath(t, p) &&
            r == Subtree(t, p) &&
            (forall x | x in PreSeqIncluding(t, p) :: x < 0) &&
            (forall x | x in PostSeqExcluding(t, p) :: x >= 0)
{
  // VERIFIED (With lemma provided in answers)
  if ( t == BSTEmpty ) { r, p := BSTEmpty, []; }
  else if ( RootValue(t) < 0 )
  {
    r, p := SearchBSTQ7(Right(t));
    if ( r == BSTEmpty ) { r, p := t, []; }
    else                 { p := [1] + p;  }
  }
  else
  {
    r, p := SearchBSTQ7(Left(t));
    p := [0] + p;
  }
}

// Q9
// Write a function in Dafny that takes two arguments, a binary
// search tree t and an integer x and returns true if the number x
// exists in the tree and returns false otherwise. You may use a
// loop or recursion, given that the reasoning is correct (i.e.
// correct requires, ensures and invariant).

method SearchBSTQ9 ( t: BST, x: int ) returns ( e: bool )
  decreases t
  requires TreeIsSorted(t)
  ensures e <==> x in TreeSeq(t)
{
  // VERIFIED
  if ( t == BSTEmpty ) { e := false; }
  else if ( RootValue(t) == x ) { e := true; }
  else if ( RootValue(t) < x )  { e := SearchBSTQ9(Right(t), x); }
  else                          { e := SearchBSTQ9(Left(t), x); }
}

// Q11
// Program the body of the function below. Use recursion and
// not a loop.
//
// 	method Root( f: real->real, a: real, b: real, eps: real )
//			returns( c: real, d: real )
//		decreases ((b-a)/eps).Floor
//		requires a < b
//		requires eps > 0.0
//		requires f(a)*f(b) <= 0.0
//		ensures a <= c < d <= b
//		ensures d-c < eps
//		ensures f(c)*f(d) <= 0.0
//
// Hint: The following lemma can be proven in Dafny. You do not
// need to call it.
//
// 	lemma BisectionTermination( a: real, b: real, eps: real )
//		requires b-a >= eps > 0.0
//		ensures ((b-a/eps).Floor > ((b-a)/2.0/eps).Floor

method Root( f: real->real, a: real, b: real, eps: real )
  returns( c: real, d: real )
  decreases ((b-a)/eps).Floor
  requires a < b // a and b are the interval of the function to find a root on
  requires eps > 0.0 // eps is precision
  requires f(a)*f(b) <= 0.0 // Must have different signs, so there is a root
  ensures a <= c < d <= b
  ensures d-c < eps
  ensures f(c)*f(d) <= 0.0
{
  // VERIFIED (With lemma and assert provided in answer)
  // The interval is small enough
  if ( b - a < eps ) { return a, b; }
  var m := a+(b-a)/2.0;
  if ( f(a)*f(m) <= 0.0 ) { c, d := Root(f, a, m, eps); }
  else { c, d := Root(f, m, b, eps); }
}

// Q12
// Program the body of the function below. Use a loop and not
// recursion. Remember to put a decreases clause in the loop.
// Consider the hint in the previous question.
//
// 	method Root( f: real->real, a: real, b: real, eps: real )
//			returns( c: real, d: real )
//		requires a < b
//		requires eps > 0.0
//		requires f(a)*f(b) <= 0.0
//		ensures a <= c < d <= b
//		ensures d-c < eps
//		ensures f(c)*f(d) <= 0.0

method RootQ12( f: real->real, a: real, b: real, eps: real )
		returns( c: real, d: real )
	requires a < b
	requires eps > 0.0
	requires f(a)*f(b) <= 0.0
	ensures a <= c < d <= b
	ensures d-c < eps
	ensures f(c)*f(d) <= 0.0
{
  // VERIFIED (With assert and lemma provided in answers)
	c, d := a, b;
	while ( d - c >= eps )
		decreases ((d-c)/eps).Floor
    invariant a <= c < d <= b
    invariant f(c)*f(d) <= 0.0
	{
		var m := c+(d-c)/2.0;
    
		if ( f(c)*f(m) <= 0.0 ) { d := m; }
		else 										{ c := m; }
	}
}