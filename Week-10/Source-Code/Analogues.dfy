// Author: Snorri Agnarsson.

// Dafny analogues of common and classic
// list processing primitives and functions.

// Usage: cons(x,y)
// Pre:   x is a value of type T,
//        y is a sequence of type seq<T>.
// Value: A sequence of type seq<T> that
//        is constructed by prepending x
//        to y.
function cons<T>( x: T, y: seq<T> ): seq<T>
{
  [x]+y
}

// Usage: car(z)
// Pre:   z is a non-empty sequence of type seq<T>.
// Value: The first value in the sequence.
function car<T>( z: seq<T> ): T
  requires z != []
  ensures car(z) == z[0]
  ensures car(z) in z
{
  z[0]
}

// Usage: cdr(z)
// Pre:   z is a non-empty sequence of type seq<T>.
// Value: The tail of the sequence.
function cdr<T>( z: seq<T> ): seq<T>
  requires z != []
  ensures cdr(z) == z[1..]
{
  z[1..]
}

// Usage: IsReverse(a,b)
// Pre:   a and b are sequences of the same type.
// Value: True iff a is the reverse of b (and vice
//        versa).
predicate IsReverse<T(==)>( a: seq<T>, b: seq<T> )
{
  |a| == |b| &&
  forall i | 0 <= i < |a| :: a[i] == b[|a|-i-1]
}

lemma ReverseLemma<T>( a: seq<T>, b: seq<T> )
  requires IsReverse(a,b)
  ensures forall i | 0 <= i <= |a| :: IsReverse(a[i..],b[..|b|-i])
{}

// Usage: Main();
// Pre:   Nothing.
// Post:  A line containing [10,9,8,7,6,5,4,3,2,1] has been written.
method Main()
{
  assert IsReverse([1,2,3],[3,2,1]);
  assert IsReverse([],cdr([1]));
  assert IsReverse<int>([],[]);
  assert !IsReverse([],[1]);
  var r := RevIota_Loop(10);
  print r;
  print "\n";
  var a := [[1,2,3],[4,5,6]];
  a := Transpose(a);
  print a;
  print "\n";
  a := [[],[]];
  a := Transpose(a);
  print a;
}

// Usage: Reverse_loop(x)
// Pre:   x is a sequence.
// Value: A sequence containing the same values as x,
//        but in reversed order.
method Reverse_loop<T>( x: seq<T> ) returns ( r: seq<T> )
  ensures IsReverse(x,r)
{
  r := [];
  var rest := x;
  ghost var done := [];
  while rest != []
    decreases |rest|
    invariant IsReverse(done,r)
    invariant x == done+rest
  {
    r := cons(car(rest),r);
    done := done+[car(rest)];
    rest := cdr(rest);
  }
}

// Usage: Append(x,y)
// Pre:   x and y are sequences of the same type.
// Value: A sequence containing the values of x and y appended.
method Append<T>( x: seq<T>, y: seq<T> ) returns ( r: seq<T> )
  ensures r == x+y
  decreases |x|
{
  if x == []
  {
    r := y;
    return;
  }
  r := Append(cdr(x),y);
  r := cons(car(x),r);
}

// Usage: Map(f,x)
// Pre:   x=[x1,...,xN] is a sequence, f is a function that
//        can take each element of x as argument.
// Value: The sequence [f(x1),...,f(xN)].
function Map<T,U>( f: T->U, x: seq<T> ): seq<U>
  requires forall z | z in x :: f.requires(z)
  ensures |x| == |Map(f,x)|
  ensures forall i | 0 <= i < |x| :: Map(f,x)[i] == f(x[i])
{
  if x == [] then
    []
  else
    cons(f(car(x)),Map(f,cdr(x)))
}

// Usage: RevMap(f,x)
// Pre:   x=[x1,...,xN] is a sequence, f is a function that
//        can take each element of x as argument.
// Value: The sequence [f(xN),...,f(x2),f(x1)].
method RevMap<T,U>( f: T->U, x: seq<T> ) returns ( r: seq<U> )
  requires forall z | z in x :: f.requires(z)
  ensures IsReverse(r,Map(f,x))
{
  r := [];
  var rest := x;
  ghost var done := [];
  while rest != []
    invariant done+rest == x
    invariant IsReverse(r,Map(f,done))
    decreases |rest|
  {
    r := cons(f(car(rest)),r);
    done := done+[car(rest)];
    rest := cdr(rest);
  }
}

// Usage: Map_loop(f,x)
// Pre:   x=[x1,...,xN] is a sequence, f is a function that
//        can take each element of x as argument.
// Value: The sequence [f(x1),...,f(xN)].
method Map_loop<T,U>( f: T->U, x: seq<T> ) returns ( r: seq<U> )
  requires forall z | z in x :: f.requires(z)
  ensures r == Map(f,x)
{
  var z := Reverse_loop(x);
  r := RevMap(f,z);
}

// Usage: FoldL(f,u,x)
// Pre:   f is a function f:UxT->U for some types U and T,
//        u is of type U, x=[x1,...,xN] is a sequence of values
//        of type T.
// Value: Where $ is the binary operation a$b = f(a,b), the value
//        is the result of computing u$x1$...$xN, computing from
//        left to right.
function FoldL<U,T>( f: (U,T)->U, u: U, x: seq<T> ): U
{
  if x == [] then
    u
  else
    FoldL(f,f(u,car(x)),cdr(x))
}

// Usage: FoldR(f,x,u)
// Pre:   f is a function f:TxU->U for some types U and T,
//        u is of type U, x=[x1,...,xN] is a sequence of values
//        of type T.
// Value: Where $ is the binary operation a$b = f(a,b), the value
//        is the result of computing x1$...$xN$u, computing from
//        right to left.
function FoldR<T,U>( f: (T,U)->U, x: seq<T>, u: U ): U
{
  if x == [] then
    u
  else
    f(car(x),FoldR(f,cdr(x),u))
}

lemma FoldL_Helper<U,T>( f: (U,T)->U, u: U, x: seq<T>, y: seq<T> )
    decreases x
    ensures FoldL(f,u,x+y) == FoldL(f,FoldL(f,u,x),y)
{
    if x==[]
    {
        assert x+y == y;
        return;
    }
    assert x+y == x[..1]+(x[1..]+y);
    FoldL_Helper(f,f(u,x[0]),x[1..],y);
}

lemma FoldL_lemma<U,T>( f: (U,T)->U, u: U, x: seq<T> )
  requires x != []
  ensures FoldL(f,u,x) == f(FoldL(f,u,x[..|x|-1]),x[|x|-1])
{
    if |x| < 2 { return; }
    assert x == x[..|x|-1]+[x[|x|-1]];
    FoldL_Helper(f,u,x[..|x|-1],x[|x|-1..]);
}

lemma FoldR_lemma<T,U>( f: (T,U)->U, x: seq<T>, u: U, y: seq<T> )
    requires IsReverse(x,y)
    decreases |x|
    ensures FoldR(f,x,u) == FoldL((a,b)=>f(b,a),u,y)
{
    if x==[] { return; }
    FoldR_lemma(f,x[1..],u,y[..|y|-1]);
    FoldL_lemma((a,b)=>f(b,a),u,y);
}

// Usage: FoldL_loop(f,u,x)
// Pre:   f is a function f:UxT->U for some types U and T,
//        u is of type U, x=[x1,...,xN] is a sequence of values
//        of type T.
// Value: Where $ is the binary operation a$b = f(a,b), the value
//        is the result of computing u$x1$x2$...$xN, computing from
//        left to right.
method FoldL_loop<U,T>( f: (U,T)->U, u: U, x: seq<T> ) returns ( r: U )
  ensures r == FoldL(f,u,x)
{
  r := u;
  var rest := x;
  ghost var done := [];
  while rest != []
    invariant r == FoldL(f,u,done)
    invariant x == done+rest
    decreases rest
  {
    FoldL_lemma(f,u,done+[car(rest)]);
    r := f(r,car(rest));
    done := done+[car(rest)];
    rest := cdr(rest);
  }
  assert x == done;
}

// Usage: FoldR_loop(f,x,u)
// Pre:   f is a function f:TxU->U for some types U and T,
//        u is of type U, x=[x1,...,xN] is a sequence of values
//        of type T.
// Value: Where $ is the binary operation a$b = f(a,b), the value
//        is the result of computing x1$x2$...$xN$u, computing from
//        right to left.
method FoldR_loop<T,U>( f: (T,U)->U, x: seq<T>, u: U ) returns ( r: U )
  ensures r == FoldR(f,x,u)
{
  var rev := Reverse_loop(x);
  FoldR_lemma(f,x,u,rev);
  r := FoldL_loop((a,b)=>f(b,a),u,rev);
}

method RevIota_Loop( n: int ) returns ( r: seq<int> )
  requires n >= 0
  // ensures r == [n,n-1,...,2,1]
  ensures |r| == n
  ensures forall i | 0 <= i < n :: r[i] == n-i
{
  var i := n;
  r := [];
  while i != 0
    // invariant 0<=i<=n, r == [n-i,n-i-1,...,2,1]
    invariant 0 <= i <= n
    invariant |r| == n-i
    invariant forall k | 0 <= k < n-i :: r[k] == n-k-i
  {
    i := i-1;
    r := cons(n-i,r);
  }
}

method Zip<R,S,T>( f: (R,S)->T, x: seq<R>, y: seq<S> ) returns( z: seq<T> )
  decreases |x|
  requires |x| == |y|
  ensures |z| == |x|
  ensures forall i | 0 <= i < |x| :: z[i] == f(x[i],y[i])
{
  if( |x| == 0 ) { return []; }
  z := Zip(f,cdr(x),cdr(y));
  z := cons(f(car(x),car(y)),z);
}

method Transpose<T>( x: seq<seq<T>> ) returns( z: seq<seq<T>> )
  decreases if |x|==0 then |x| else |x[0]|
  requires forall i,j | 0 <= i < j < |x| :: |x[i]| == |x[j]|
  ensures forall i | 0 <= i < |x| :: |x[i]| == |z|
  ensures forall j | 0 <= j < |z| :: |z[j]| == |x|
  ensures forall i,j | 0 <= i < |x| && 0 <= j < |z| :: x[i][j] == z[j][i]
{
  if( |x| == 0 || |x[0]| == 0 ) { return []; }
  var heads := Map_loop((u)=>if u==[] then x[0][0] else car(u),x);
  var tails := Map_loop((u)=>if u==[] then [] else cdr(u),x);
  tails := Transpose(tails);
  z := cons(heads,tails);
}