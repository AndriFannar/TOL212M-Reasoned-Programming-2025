public class E13
{
    // Notkun: int q = partition(a,i,j);
    // Fyrir:  a[i..j) er ekki-tómt svæði sem inniheldur
    //         löglega E hluti.
    // Eftir:  i <= q < j.
    //         Svæðið a[i..j) inniheldur sömu hluti eftir
    //         sem áður, en búið er að endurraða þeim þ.a.
    //         a[i..q) <= a[q] <= a(q..j).

    // Usage:  int q = partition(a,i,j);
    // Pre:    a[i..j) is a non-empty section that contains
    //         legal E objects.
    // Post:   i <= q < j.
    //         The section a[i..j) contains the same objects
    //         as before, but they have been permuted so that
    //         a[i..q) <= a[q] <= a(q..j).
    public static<E extends Comparable<? super E>>
    int partition( E[] a, int i, int j )
    {
        // Hér vantar útfærslu.
        // Eðlilegt er að nota lykkju og einhverja aðferð
        // sem auðvelt er að rökstyðja með fastayrðingu.
        // Aðferð Lomutos er trúlega auðveldust.
        // Here we need an implementation.
        // It is natural to use a loop and some method
        // that can easily be verified using an invariant.
        // Lomuto's method is probably easiest.
        int q = i+1;
        E p = a[i];
        for( int r = q ; r != j ; r++ )
            // |p| <p | >=p | ??? |
            //  i      q     r     j
            if( a[r].compareTo(p) < 0 )
            {
                E tmp = a[q];
                a[q++] = a[r];
                a[r] = tmp;
            }
        a[i] = a[--q];
        a[q] = p;
        return q;
    }

    // Notkun: quickSelectRecursive(a,i,k,j);
    // Fyrir:  0 <= i <= k < j <= a.length.
    //         Svæðið a[i..j) inniheldur löglega E hluti.
    // Eftir:  Svæðið a[i..j) inniheldur sömu hluti, en
    //         búið er að endurraða þannig að
    //           a[i..k) <= a[k] <= a(k..j).

    // Usage:  quickSelectRecursive(a,i,k,j);
    // Pre:    0 <= i <= k < j <= a.length.
    //         The section a[i..j) contains legal E objects.
    // Post:   The section a[i..j) contains the same objects,
    //         but they have been permuted so that
    //           a[i..k) <= a[k] <= a(k..j).
    public static<E extends Comparable<? super E>>
    void quickSelectRecursive( E[] a, int i, int k, int j )
    {
        // Hér vantar útfærslu sem skal vera endurkvæm
        // og án lykkju.
        // Notið fallið partition að ofan.
        // Ekki skal fullraða svæðinu.
        // Eðlileg útfærsla mun hafa meðaltímaflækju
        // O(n) fyrir slembin gögn.
        // Here we need an implementation that should
        // be recursive and without a loop.
        // Use the partition function above.
        // Do not fully sort the section.
        // A natural implementation would have an
        // average time complexity of O(n) for
        // random data.
        if( j-i == 1 ) return;
        int q = partition(a,i,j);
        if( k < q )
            quickSelectRecursive(a,i,k,q);
        else if( k > q )
            quickSelectRecursive(a,q+1,k,j);
    }

    // Sama lýsing og að ofan, fyrir utan nafn fallsins.
    // Same description as above, except for the name of the function.
    public static<E extends Comparable<? super E>>
    void quickSelectLoop( E[] a, int i, int k, int j )
    {
        // Hér vantar útfærslu sem skal vera án endurkvæmni.
        // Notið lykkju til að þrengja að sætinu k.
        // Notið fallið partition að ofan.
        // Munið að skrifa skýra og skilmerkilega fastayrðingu.
        // Ekki skal fullraða svæðinu.
        // Eðlileg útfærsla mun hafa meðaltímaflækju
        // O(n) fyrir slembin gögn.
        // Here we need an implementation that should be
        // without recursion. Use a loop to constrain
        // position k. Use the partition function above.
        // Remember to write a clear and complete loop
        // invariant. Do not fully sort the section.
        // A natural implementation will have average
        // time complexity O(n) for random data.
        int p = i, q = j;
        while( j-i > 1 )
            // |  A  |  B  |  C  |
            //  i     p     q     j
            //
            // Allt í A er <= allt í B og C.
            // Allt í C er >= allt í A og B.
            // All in A is <= all in B and C.
            // All in C is >= all in A and B.
            //   i <= p <= k < q <= j
        {
            int r = partition(a,p,q);
            if( k < r )
                q = r;
            else if( k > r )
                p = r+1;
            else
                return;
        }
    }
    
    public static void main( String[] args )
    {
        int k = Integer.parseInt(args[0]);
        if( k < 1 || k >= args.length ) throw new Error("Invalid input index");
        quickSelectLoop(args,1,k,args.length);
        for( int i = 1 ; i != args.length ; i++ ) System.out.print(args[i]+" ");
    }
}