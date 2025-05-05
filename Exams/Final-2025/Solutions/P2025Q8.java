public class P2025Q8
{
    // Usage: BSTNode r = leftmostPositive(t);
    // Pre:   t is a binary search tree.
    // Post:  r refers to the leftmost node in t that has a positive value.
    //        If no such node exists then r is null.
    public static BSTNode leftmostPositive( BSTNode t )
    {
        if( t == null ) return null;
        if( BSTNode.rootValue(t) <= 0 ) return leftmostPositive(BSTNode.right(t));
        BSTNode r = leftmostPositive(BSTNode.left(t));
        if( r != null ) return r;
        return t;
    }
}