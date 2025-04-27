/*
Write a recursive binary search function in Java with the following description:
  // Usage:  int k = find(a,i,n,x);
  // Pre:    0 <= i <= i+n <= a.length, x is an int,
  //         a[i..i+n) is in ascending order. (In Dafny we would
  //         write a[i..i+n] instead of a[i..i+n).) 
  // Post:   i <= k <= i+n.
  //         a[i..k) <= x < a[k..i+n). 
  //         The array a is unchanged.
  static int find( int[] a, int i, int n, int x )
  {
    …
  }
*/

public class P2023Q3
{
    // Usage:  int k = find(a,i,n,x);
    // Pre:    0 <= i <= i+n <= a.length, x is an int,
    //         a[i..i+n) is in ascending order. (In Dafny we would
    //         write a[i..i+n] instead of a[i..i+n).) 
    // Post:   i <= k <= i+n.
    //         a[i..k) <= x < a[k..i+n). 
    //         The array a is unchanged.
    static int find( int[] a, int i, int n, int x )
    {
        if( n == 0 ) return i;
        int n2 = n/2;
        if( a[i+n2] <= x )
            return find(a,i+n2+1,n-n2-1,x);
        else
            return find(a,i,n2,x); 
    }  
}