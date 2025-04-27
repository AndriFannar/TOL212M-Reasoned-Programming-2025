/*
  public class BSTNode {
    private BSTNode left,right;
    private int val;
    public BSTNode( BST a, int x, BST b )
    { left=a; val=x; right=b; }
    public static left( BSTNode t ) { return t.left; }
    public static right( BSTNode t ) { return t.right; }
    public static rootValue( BSTNode t ) { return t.val; }
  }
Solve the same problem as above, but this time in Java. Use our familiar definition of tree nodes, as seen above.
*/

public class P2023Q8
{
    // Usage: BSTNode r = findLastNegative(t);
    // Pre:   t is a binary search tree.
    // Post:  r refers to the rightmost node in t that has a negative value
    //        unless no such node exists, in which case r is null.
    public static BSTNode findLastNegative( BSTNode t )
    {
        if( t == null ) return null;
        if( BSTNode.rootValue(t) < 0 )
        {
            BSTNode r = findLastNegative(BSTNode.right(t));
            if( r == null) return t;
            else           return r;
        }
        return findLastNegative(BSTNode.left(t));
    }
}