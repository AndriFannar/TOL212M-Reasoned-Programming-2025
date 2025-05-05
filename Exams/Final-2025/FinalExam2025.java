public class FinalExam2025
{
  // Q3
  // Write a recursive binary search function in Java with the 
  // following description:
  //  Usage: int k = find(a, i, n, x);
  //  Pre:   0 <= i <= i+n <= a.length, x is an int,
  //         a[i..i+n) is in ascending order and 
  //         has no duplicate values.
  //  Post:  i <= k <= i+n
  //         If x is in a[i..i+n] then k is the position
  //         that contains x, otherwise k is the position
  //         which should contain x to maintain order,
  //         such that all positions before contain
  //         values <x.
  static int find( int[] a, int i, int n, int x )
  {
    if (n == 0) return i;
    int n2 = n/2;
    if (a[i+n2] > /* Should be < */ x) return find(a, i+n2+1, n-n2-1, x);
    else return find(a, i, n2, x);
  }


  // Q8
  // Solve the same problem as above (Q7), but this time in Java. Use our
  // familiar definition of tree nodes, as seen below.
  // (I am skipping Usage/Pre/Post to save space bacause they are
  // familiar and obvious. Note that this does not mean that students
  // can skip writing familiar and obvious descriptions for their 
  // classes.)
  //
  //  public class BSTNode {
  //    private BSTNode left, right;
  //    private int val;
  //    public BSTNode( BSTNode a, int x, BSTNode b)
  //    { left=a; val=x; right=b; }
  //    public static BSTNode left( BSTNode t ) { return t.left; }
  //    public static BSTNode right( BSTNode t ) { return t.right; }
  //    public static int rootValue( BSTNode t) { return t.val; }
  //  }

  // Usage: BSTNode n = searchBSTQ8(t);
  // Pre:   t is a Binary Search Tree.
  // Post:  k is the leftmost node in t which contains a
  //        value greater than 0, if it exists.
  //        Otherwise, k is null.
  static BSTNode searchBSTQ8(BSTNode t)
  {
    if (t == null) return null;
    if (BSTNode.rootValue(t) <= 0) return searchBSTQ8(BSTNode.right(t));
    else
    {
      BSTNode tp = searchBSTQ8(BSTNode.left(t));
      if (tp == null) return t;
      return tp;
    }
  }


  // Q10
  // Solve the same problem as above (Q9), but in Java.
  
  // Usage: boolean n = SearchBSTQ10(t);
  // Pre:   t is a Binary Search Tree.
  // Post:  n is true if t contains a node with a
  //        root vale less than zero, false otherwise.
  static boolean searchBSTQ10( BSTNode t )
  {
    if ( t == null )                return false;
    if ( BSTNode.rootValue(t) < 0 ) return true;
    else return searchBSTQ10(BSTNode.left(t));
  } 
}