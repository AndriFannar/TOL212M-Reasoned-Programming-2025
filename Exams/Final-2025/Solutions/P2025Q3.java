public class P2025Q3
{
    // Notkun: int k = find(a,i,n,x);
    // Fyrir:  0 <= i <= i+n <= a.length, x er heiltala,
    //         a[i..i+n) er í vaxandi röð og inniheldur
    //         engar endurtekningar.
    // Eftir:  i <= k <= i+n.
    //         Ef x er í a[i..i+n) þá er k sætið sem
    //         inniheldur x, annars er k sætið þar sem x
    //         ætti að vera til að halda röðun, þ.a. öll
    //         fremri sæti innihalda gildi <x.
    // Usage:  int k = find(a,i,n,x);
    // Pre:    0 <= i <= i+n <= a.length, x is an int,
    //         a[i..i+n) is in ascending order and 
    //         has no duplicate values.
    // Post:   i <= k <= i+n.
    //         If x is in a[i..i+n) then k is the position 
    //         that contains x, otherwise k is the position
    //         which should contain x to maintain order,
    //         such that all positions before contain
    //         values <x.
    static int find( int[] a, int i, int n, int x )
    {
        if( n == 0 ) return i;
        int n2 = n/2;
        if( a[i+n2] < x ) 
            return find(a,i+n2+1,n-n2-1,x);
        else
            return find(a,i,n2,x);
    }
}