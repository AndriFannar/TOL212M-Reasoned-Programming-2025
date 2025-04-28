/*
Solve the same problem as above, but in Java.
*/

public class P2023Q10
{
    // Usage: boolean r = Find( BSTNode t, int x );
    // Pre:   t is a binary search tree.
    // Post:  r is true if and only if x is in t.
    static public boolean find( BSTNode t, int x )
    {
        if( t == null ) return false;
        if( BSTNode.rootValue(t) == x )     return true;
        else if( BSTNode.rootValue(t) < x ) return find(BSTNode.right(t),x);
        else                                return find(BSTNode.left(t),x);
    } 
}