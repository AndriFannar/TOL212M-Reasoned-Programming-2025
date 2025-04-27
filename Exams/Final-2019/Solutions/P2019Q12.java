public class P2019Q12
{
    // Notkun: int m = max(a);
    // Fyrir:  a er fylki heiltalna, ekki tómt.
    // Eftir:  m er stærsta talan í a.
    // Ath.:   Svipað fall í Dafny er að finna
    //         hér:
    //         https://rise4fun.com/Dafny/B2DV0
    static int max( int[] a )
    {
        int m = a[0];
        for( int i=1 ; i!=a.length ; i++ )
            // 1 <= i <= a.length.
            // m er stærsta talan í a[0..i).
            if( a[i] > m ) m = a[i];
        return m;
    }
}