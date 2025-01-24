public class BinarySearchJava {

    // Notkun: int k = searchRecursive(a,i,j,x);
    // Fyrir: a[i..j-1] er svæði í a, í minnkandi röð.
    // Eftir: i <= k <= j,
    // öll gildi í a[i..k-1] eru >=x,
    // öll gildi í a[k..j-1] eru <x.
    static int searchRecursive( double[] a, int i, int j, double x )
    {
        if( i == j ) return ?A?;
        int m = ?B?;
        if( a[m] ?C? x )
            return searchRecursive(a,i,?D?,x);
        else
            return searchRecursive(a,?E?,j,x);
    }

    // Notkun: int k = searchLoop(a,i,j,x);
    // Fyrir: a[i..j-1] er svæði í a, í minnkandi röð.
    // Eftir: i <= k <= j,
    // öll gildi í a[i..k-1] eru >=x,
    // öll gildi í a[k..j-1] eru <x.
    static int searchLoop( double[] a, int i, int j, double x )
    {
        int p = ?F?;
        int q = ?G?;
        while( ?H? )
            // Loop invariant:
            //    ?I?
        {
            int m = ?J?;
            if( a[m] ?K? x )
                p = ?L?;
            else
                q = ?M?;
        }
        return ?N?;
    }
}