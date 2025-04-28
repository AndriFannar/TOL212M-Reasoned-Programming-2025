include "BST.dfy"
// Q1
// Write a method in Dafny that searches with Binary Search in an integer
// sequence a, which is in descending order, for the last position that
// contains a value >= 100. If no such position exists then return -1.

method BinarySearch( a: seq<int> ) returns ( k: int )
  decreases |a|
  requires forall p,q | 0 <= p <= q < |a| :: a[p] > a[q]
  ensures k == -1 ==> forall p | 0 <= p < |a| :: a[p] < 100
  ensures k != -1 ==>
            0 <= k < |a| &&
            a[k] >= 100
  // | >= 100 | ??? | <100 |
  //  0        p     q     |a|
{
  // VERIFIED
  if (a == []) { return -1; }
  var m := |a|/2;
  if (a[m] >= 100)
  {
    k := BinarySearch(a[m+1..]);
    if ( k == -1 ) { return m; }
    k := k+m+1;
  }
  else { k := BinarySearch(a[..m]); }
}

// Q2
// Write a Binary Search method in Dafny that takes three arguments, an integer
// sequence s in ascending order, two integers a and b with a<=b, which returns
// an index to some position in the sequence containing a value x such that a <= x <= b.
// If no such position exists then return -1.

method BinarySearch2( s: seq<int>, a: int, b: int ) returns ( k: int )
  requires a <= b
  requires forall p,q | 0 <= p <= q < |s| :: s[p] <= s[q]
  ensures k == -1 ==> forall x | x in s :: x < a || x > b
  ensures k != -1 ==>
            0 <= k < |s| &&
            a <= s[k] <= b
{
  // VERIFIED (With asserts from answers)
  if ( s == [] ) { return -1; }
  var m := |s|/2;
  if ( a <= s[m] <= b ) { return m; }
  if ( s[m] < a )
  {
    k := BinarySearch2( s[ m+1.. ], a, b);
    if ( k != -1 ) { k := k+m+1; }
  }
  else { k := BinarySearch2( s[..m], a, b ); }
}

// Q3
// Assume the existence of the following Dafny method.
//		method Partition ( s: seq<int> )
//			returns ( a: seq<int>
//					, p: int
//					, b: seq<int>
//					, q: int
//					, c: seq<int>
//					)
//		  requires |s| >= 2
//		  ensures p <= q
//		  ensures forall z | z in a :: z < p
//		  ensures forall z | z in b :: p <= z <= q
//		  ensures forall z | z in c :: q < z
//		  ensures multiset(s) ==
//					multiset(a) +
//					multiset{p} +
//					multiset(b) +
//					multiset{q} +
//					multiset(c)
// Write a Quicksort method that takes a sequence of integers ( seq<int> )
// as an argument and returns an ascending sequence of the same numbers
// and uses this Partition method as a helper method. The Partition method
// need not be written.

method Quicksort( s: seq<int> ) returns ( s': seq<int>)
  decreases |s|
  ensures forall p,q | 0 <= p <= q < |s'| :: s'[p] <= s'[q]
  ensures multiset(s) == multiset(s')
{
  // VERIFIED (With asserts from answers)
  if ( |s| < 2 ) { return s; }
  var a, p, b, q, c := Partition( s );
  var a' := Quicksort( a );
  var b' := Quicksort( b );
  var c' := Quicksort( c );
  s' := a' + [p] + b' + [q] + c';
}

// Q4
// Program the Partition method described above. Remember that loops need an invariant

method Partition ( s: seq<int> )
  returns ( a: seq<int>
          , p: int
          , b: seq<int>
          , q: int
          , c: seq<int>
  )
  requires |s| >= 2
  ensures p <= q
  ensures forall z | z in a :: z < p
  ensures forall z | z in b :: p <= z <= q
  ensures forall z | z in c :: q < z
  ensures multiset(s) ==
          multiset(a) +
          multiset{p} +
          multiset(b) +
          multiset{q} +
          multiset(c)
{
  // VERIFIED (With asserts from answers)
  if ( |s| == 2 )
  {
    a, b, c := [], [], [];
    if ( s[0] <= s[1] ) { p, q := s[0], s[1]; }
    else { p, q := s[1], s[0]; }
    return;
  }

  var x := s[0];
  a, p, b, q, c := Partition(s[1..]);
  if ( p <= x <= q ) { b := b + [x]; }
  else if ( x < p ) { a := a + [x]; }
  else { c := c + [x]; }
}

// Q5
// Assume the definition
//		datatype BST = BSTEmpty | BSTNode(BST, int, BST)
// as in our file BST.dfy. Assume also the functions IsTreePath,
// PreSeq, MidSeq, etc., that use tree paths to segment a tree
// (definitions are at the end of the exam).
// Write a function that searches using a loop in a binary search
// tree and returns the rightmost node containing a <100, or
// returns BSTEmpty if no such node exists in the search tree.
// Remember to write a full description with requires/ensures
// and write an invariant for the loop.

method Search100 ( t: BST ) returns ( st: BST )
  requires TreeIsSorted(t)
  ensures st == BSTEmpty ==> forall z | z in TreeSeq(t) :: z >= 100
  ensures st != BSTEmpty ==>
            (exists rp | IsTreePath(t,rp) ::
               st == Subtree(t,rp) &&
               (forall z | z in PreSeqIncluding(t, rp) :: z < 100) &&
               (forall z | z in PostSeqExcluding(t, rp) :: z >= 100))
{
  // VERIFIED (With asserts and lemmas from answers)
  var p: seq<dir> := [];
  var sp: seq<dir> := [];
  st := BSTEmpty;
  var s := t;

  while ( s != BSTEmpty )
    decreases s
    invariant IsTreePath(t, p)
    invariant s == Subtree(t, p)
    invariant TreeIsSorted(s)
    invariant forall z | z in PreSeq(t, p) :: z < 100
    invariant forall z | z in PostSeq(t, p) :: z >= 100
    invariant st == BSTEmpty ==> PreSeq(t, p) == []
    invariant st != BSTEmpty ==>
                IsTreePath(t, sp) &&
                st == Subtree(t, sp) &&
                PreSeq(t, p) == PreSeqIncluding(t, sp)
  {
    if ( RootValue(s) < 100 )
    {
      st := s;
      sp := p;
      s := Right(s);
      p := p + [1];
    }
    else
    {
      s := Left(s);
      p := p + [0];
    }
  }
}

// Q6
// Assume the same BST definitions as above. Write a Dafny
// method that takes three arguments, a binary search tree t, and
// integers a, b with a<=b. The method should return a subtree t that
// has a root value x such that a <= x <= b, if such a subtree exists.
// Otherwise, return BSTEmpty. You may have more return values if
// you wish, but that is not neccesary

method Search( t: BST, a: int, b: int ) returns ( ghost rp: seq<dir>, r: BST )
  decreases t
  requires a <= b
  requires TreeIsSorted(t)
  ensures r == BSTEmpty ==> forall z | z in TreeSeq(t) :: z < a || z > b
  ensures r != BSTEmpty ==>
            IsTreePath(t, rp) &&
            r == Subtree(t, rp) &&
            a <= RootValue(r) <= b
{
  // VERIFIED (With lemmas from answers)
  if ( t == BSTEmpty )
  {
    rp := [];
    r := BSTEmpty;
    return;
  }
  if ( a <= RootValue(t) <= b )
  {
    r := t;
    rp := [];
  }
  else if ( RootValue(t) < a )
  {
    rp, r := Search( Right(t), a, b);
    rp := [1] + rp;
  }
  else
  {
    rp, r := Search( Left(t), a, b );
    rp := [0] + rp;
  }
}

// Q7
// Finish programming the following Dafny method.

method Min ( x: seq<int> ) returns ( m: int )
  requires |x| > 0
  ensures m in x
  ensures forall j | 0 <= j < |x| :: x[j] >= m
{
  // VERIFIED
  if ( |x| == 1 ) { return x[0]; }
  m := x[0];
  var mp := Min(x[1..]);
  if ( m > mp ) { m := mp; }
}