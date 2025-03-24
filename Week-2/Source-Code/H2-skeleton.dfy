// Author of question: Snorri Agnarsson
// Permalink of question: https://tinyurl.com/3xz4kd2p

// Authors of solution:   ...
// Permalink of solution: ...
// Use the command
//   dafny build H2-skeleton.dfy
// to compile the file.
// Or use the web page tio.run/#dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file or email the solution to me.

method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    decreases ???
    requires ???
    ensures ???
{
    ???
}

method SearchLoop( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires ???
    ensures ???
{
    var p := ???;
    var q := ???;
    while ???
        decreases ???
        invariant ???
    {
        ???
    }
    return ???;
}

// Ef eftirfarandi fall er ekki samþykkt þá eru
// föllin ekki að haga sér rétt að mati Dafny.

// If the following method is not accepted then
// the functions are not behaving correctly in
// Dafny's opinion.

method Test( a: seq<real>, x: real )
    requires forall p,q | 0 <= p < q < |a| :: a[p] >= a[q]
{
    var k1 := SearchLoop(a,0,|a|,x);
    assert forall r | 0 <= r < k1 :: a[r] >= x;
    assert forall r | k1 <= r < |a| :: a[r] < x;
    var k2 := SearchRecursive(a,0,|a|,x);
    assert forall r | 0 <= r < k2 :: a[r] >= x;
    assert forall r | k2 <= r < |a| :: a[r] < x;
}