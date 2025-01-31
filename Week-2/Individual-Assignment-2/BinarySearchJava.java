public class BinarySearchJava {

    // Notkun: int k = searchRecursive(a,i,j,x);
    // Fyrir: a[i..j-1] er svæði í a, í minnkandi röð.
    // Eftir: i <= k <= j,
    // öll gildi í a[i..k-1] eru >=x,
    // öll gildi í a[k..j-1] eru <x.
    static int searchRecursive(double[] a, int i, int j, double x) {
        if (i == j)
            return i; // ?A?;
        int m = i + (j - i) / 2; // ?B?;
        if (a[m] < x)// ?C? x )
            return searchRecursive(a, i, m, x);// ?D?,x);
        else
            return searchRecursive(a, m + 1, j, x);// ?E?,j,x);
    }

    // Notkun: int k = searchLoop(a,i,j,x);
    // Fyrir: a[i..j-1] er svæði í a, í minnkandi röð.
    // Eftir: i <= k <= j,
    // öll gildi í a[i..k-1] eru >=x,
    // öll gildi í a[k..j-1] eru <x.
    static int searchLoop(double[] a, int i, int j, double x) {
        int p = i;// ?F?;
        int q = j;// ?G?;
        while (p != q)// ?H? )
        // Loop invariant:
        // a[i..p-1] >= x > a[q..j-1] ?I?
        {
            int m = p + (q - p) / 2;// ?J?;
            if (a[m] >= x)// ?K? x )
                p = m + 1; // ?L?;
            else
                q = m;// ?M?;
        }
        return p;// ?N?;
    }
}