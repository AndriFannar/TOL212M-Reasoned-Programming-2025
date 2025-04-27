/*
Write a function in Dafny that takes two arguments, a binary search tree t and 
an integer x and returns true if the number x exists in the tree and returns 
false otherwise. You may use a loop or recursion, given that the reasoning is 
correct (i.e. correct requires, ensures and invariant).
*/

include "BST.dfy"

method Find( t: BST, x: int ) returns( r: bool )
    requires TreeIsSorted(t)
    ensures r <==> x in TreeSeq(t)
{
    if t == BSTEmpty { return false; }
    if RootValue(t) == x { return true; }
    if RootValue(t) < x { r := Find(Right(t),x); }
    else                { r := Find(Left(t),x);  }
}