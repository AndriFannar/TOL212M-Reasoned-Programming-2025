public class P2025Q10
{
    // Usage: bool r = hasNegative(t);
    // Pre:   t is a binary search tree.
    // Post:  r is true if and only if t contains a negative value.
    public static bool hasNegative( t: BSTNode )
    {
        if( y == null ) return false;
        if( BSTNode.rootValue(t) < 0 ) return true;
        return hasNegative(BSTNode.left(t));
    }
}