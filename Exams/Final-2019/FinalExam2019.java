public class FinalExam2019 {
  // Q3
	// Write a recursive Binary Search function in Java
	// which has the following description:
	//
	// Usage: int k = find(a,i,n,x);
	// Pre:   0 <= i <= i+n <= a.length, x is an integer,
	//        a[i..i+n] is in ascending order. (In Dafny we would
	//        write a[i..i+n] instead of a[i..i+n].)
	//				n >= 0 and n+1 is a power of two, i.e. possible
	//				values for n are 0, 1, 3, 7, 15, 31, etc.
	// 	Post:  i <= k <= i+n.
	// 				 a[i..k) < x <= a[k..i+n).
	// 				 The array a is unchanged.
	//	static int find( int[] a, int i, int n, int x)
	//  {
	//		...
	//  }
	
	// Usage: int k = find(a,i,n,x);
	// Pre:   0 <= i <= i+n <= a.length, x is an integer,
	//        a[i..i+n] is in ascending order. (In Dafny we would
	//        write a[i..i+n] instead of a[i..i+n].)
	//				n >= 0 and n+1 is a power of two, i.e. possible
	//				values for n are 0, 1, 3, 7, 15, 31, etc.
	// 	Post: i <= k <= i+n.
	// 				a[i..k) < x <= a[k..i+n).
	// 				The array a is unchanged.
	static int find( int[] a, int i, int n, int x)
	{
		if ( n == 0 ) return i;
		int n2 = n/2;
		if ( a[i+n2] < x ) return find(a, i+n2+1, n2, x);
		else return find(a, i, n2, x);
	}
}
