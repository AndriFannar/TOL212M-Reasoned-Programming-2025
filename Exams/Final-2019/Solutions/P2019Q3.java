public class P2019Q3
{
    // Notkun: int k = find(a,i,n,x); 
    // Fyrir: 0 <= i <= i+n <= a.length, x er heiltala, 
    //        a[i..i+n) er í vaxandi röð. (Í Dafny myndum við 
    //        skrifa a[i..i+n] í stað a[i..i+n).) 
    //        n >= 0 og n+1 er veldi af tveimur, þ.e. lögleg 
    //        gildi fyrir n eru 0,1,3,7,15,31, o.s.frv. 
    // Eftir: i <= k <= i+n. 
    //        a[i..k) < x <= a[k..i+n). 
    //        Fylkið a er óbreytt. 
    static int find( int[] a, int i, int n, int x )
    {
        if( n == 0 ) return i;
        if( a[i+n/2] < x )
            return find(a,i+n/2+1,n/2,x);
        else
            return find(a,i,n/2,x);
    }
}