public class FinalExam2023 {
	// Q3
	// Write a recursive binary search function in Java with the following
	// description:
	// 	Usage: int k = find(a,i,n,x);
	// 	Pre:   0 <= i <= i+n <= a.length, x is an int,
	// 				 a[i..i+n) is in ascending order. (In Dafny we would
	//         write a[i..i+n] instead of a[i..i+n].)
	// 	Post:  i <= k <= i+n.
	// 				 a[i..k) <= x < a[k..i+n).
	// 				 The array a is unchanged.
	static int find( int[] a, int i, int n, int x)
	{
		if ( n == 0 ) return i;
		int n2 = n/2;
		if ( a[i+n2] <= x )
		{
			return find(a, i+n2+1, n-n2-1, x);
		}
		else
		{
			return find(a, i, n2, x);
		}
	}
	
	// Q8
	// Solve the same problem as above (Q7), but this time in Java. Use our
	// familiar definition of tree nodes, as seen above.
	// (I am skipping Usage/Pre/Post to save space because they are
	// familiar and obvious. Note that this does not mean that students
	// can skip writing familiar and obvious descriptions for their
	// classes.)
	
	// Usage: BSTNode p = searchBSTQ8(t);
	// Pre:   t is a Binary Search Tree.
	// Post:  p is the rightmost node that contains a number less than zero,
	//        if it exists. If no such number exists, p is null.
	static BSTNode searchBSTQ8( BSTNode t )
	{
		if ( t == null ) return null;
		if ( BSTNode.rootValue(t) < 0 )
		{
			BSTNode r = searchBSTQ8(BSTNode.right(t));
			if ( r == null ) return t;
			return r;
		}
		return searchBSTQ8(BSTNode.left(t));
	}
	
	// Q10
	// Solve the same problem as above (Q9), but in Java.
	
	// Usage: boolean e = searchBSTQ10(t,x);
	// Pre:   t is a Binary Search Tree.
	// Post:  e is true if x exists in t, otherwise is false.
	static boolean searchBSTQ10( BSTNode t, int x )
	{
		if ( t == null ) return false;
		if ( BSTNode.rootValue(t) == x ) return true;
		if ( BSTNode.rootValue(t) < x )  return searchBSTQ10(BSTNode.right(t), x);
		else 														 return searchBSTQ10(BSTNode.left(t), x);
	}
}

