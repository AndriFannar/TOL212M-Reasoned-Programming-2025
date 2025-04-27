// Klasinn E11 notar klasann Link sem er í Link.java.
// Lesið skilgreiningarnar og setningarnar þar.

public class E11
{    
    // Notkun: splice(x,i,y);
    // Fyrir:  x er lögleg keðja með N hlekki og hlekkjarunu
    //           [x_0,...,x_{N-1}].
    //         0 <= i < N.
    //         y er lögleg keðja með M hlekki og hlekkjarunu
    //           [y_0,...,y_{M-1}].
    //         Keðjurnar x og y hafa engan sameiginlegan hlekk.
    // Eftir:  x er lögleg keðja með N+M hlekki og hlekkjarununa
    //           [x_0,...,x_i,y_0,...,y_{M-1},x_{i+1},...,x_{N-1}].
    //         Takið eftir að y rununni er splæst inn í x rununa
    //         með i+1 hlekki fyrir framan úr gömlu x rununni.
    //         Takið eftir að leyfilegt er að y sé tóm runa.
    //         Takið eftir að engir nýjir hlekkir verða til.
    // Usage:  splice(x,i,y);
    // Pre:    x is a legal chain with N>0 links and a sequence of links
    //           [x_0,...,x_{N-1}].
    //         0 <= i < N.
    //         y is a legal chain with M links and a sequence of links
    //           [y_0,...,y_{M-1}].
    //         The chains x and y have no links in common.
    // Post:   x is a legal chain with N+M links and the sequence of links
    //           [x_0,...,x_i,y_0,...,y_{M-1},x_{i+1},...,x_{N-1}].
    //         Note that the y sequence is spliced into the x sequence
    //         with i+1 links from x in front of the spliced y sequence.
    //         Note that y is allowed to be empty.
    //         Note that no new links are created.
    public static<E> void splice( Link<E> x, int i, Link<E> y )
    {
        if( y == null ) return;
        int k = 0;
        while( k != i )
            // 0 <= k <= i.
            // x vísar á hlekk númer k í upphaflegu
            // hlekkjakeðju x.
            // x refers to the k-th link in the
            // original chain x.
        {
            x = x.tail;
            k++;
        }
        Link<E> z = x.tail;
        x.tail = y;
        // z er lögleg keðja með hlekkjarununni
        //  [x_{i+1},...,x_{N-1}], miðað við upphaflega x.
        // x er lögleg keðja með hlekkjarununni
        //  [x_0,...,x_i,y_0,...,y_{M-1}].
        // y er óbreytt og er ekki tóm.
        // z is a legal chain with the sequence
        // of links [x_{i+1},...,x_{N-1}], from the
        // original chain x.
        // x is a legal chain with the sequence of
        // links [x_0,...,x_i,y_0,...,y_{M-1}].
        // y is unchanged and is not empty.
        while( y.tail != null )
            // y vísar á einhvern hlekk í upphaflega y,
            // sem er þá einnig hlekkur í núverandi x.
            // x og z eru eins og lýst er að ofan.
            // y refers to some link in the original y,
            // which is then also a link in the current x.
            // x and z are as described above.
        {
            y = y.tail;
        }
        y.tail = z;
    }
    
    // Notkun: Link<E> x = makeChainLoop(a);
    // Fyrir:  a er E[], ekki null.
    // Eftir:  x er lögleg keðja með N=a.length hlekki og
    //         hlekkjarunu nýrra hlekkja [h_0,...,h_{N-1}] þannig
    //         að h_I.head == a[I] fyrir I=0,...,N-1.
    // Usage:  Link<E> x = makeChainLoop(a);
    // Pre:    a is E[], not null.
    // Post:   x is a legal chain with N=a.length links and
    //         a sequence [h_0,...,h_{N-1}] of new links such
    //         that h_I.head == a[I] for I=0,...,N-1.
    public static<E> Link<E> makeChainLoop( E[] a )
    {
        int i = a.length;
        Link<E> r = null;
        while( i != 0 )
            // r er lögleg keðja N==a.length-i nýrra hlekkja og hlekkjarunu
            // [h_0,...,h_{N-1}] þannig að fyrir k=0,...,N-1 gildir að
            // h_k.head == a[i+k].
            // r is a legal chain with N=a.length-i new links and the
            // sequence of links [h_0,...,h_{N-1}] such that for k=0,...,N-1
            // we have h_k.head == a[i+k].
        {
            Link<E> tmp = new Link<E>();
            tmp.tail = r;
            tmp.head = a[--i];
            r = tmp;
        }
        return r;
    }
    
    // Notkun: Link<E> x = makeChainRecursive(a,i,j);
    // Fyrir:  a er E[], ekki null, og a[i..j) er svæði í a.
    //         (Athugið að þá er 0 <= i <= j <= a.length).
    // Eftir:  x er lögleg keðja með N=j-i hlekki og
    //         hlekkjarunu nýrra hlekkja [h_0,...,h_{N-1}] þannig
    //         að h_I.head == a[I-i] fyrir I=0,...,N-1.
    // Usage:  Link<E> x = makeChainRecursive(a,i,j);
    // Pre:    a is E[], not null, and a[i..j) is a section of a.
    //         (Note that we have 0 <= i <= j <= a.length).
    // Post:   x is a legal chain with N=j-i links and a sequence
    //         of new links [h_0,...,h_{N-1}] such that
    //         h_I.head == a[I-i] for I=0,...,N-1.
    public static<E> Link<E> makeChainRecursive( E[] a, int i, int j )
    {
        if( i == j ) return null;
        Link<E> r = new Link<E>();
        r.tail = makeChainRecursive(a,i+1,j);
        r.head = a[i];
        return r;
    }
    
    // Prófið að keyra þessa skipun:
    //  java E11 1 2 3 4 5 6
    // það ætti að skrifa
    //  1 2 3 4 1 2 3 4 5 6 5 6
    // Try running this command:
    //  java E11 1 2 3 4 5 6
    // this should write
    //  1 2 3 4 1 2 3 4 5 6 5 6
    public static void main( String[] args )
    {
        Link<String> x = makeChainLoop(args);
        Link<String> y = makeChainRecursive(args,0,args.length);
        splice(x,3,y);
        splice(x,0,null);
        while( x != null )
        {
            System.out.print(x.head+" ");
            x = x.tail;
        }
    }
}