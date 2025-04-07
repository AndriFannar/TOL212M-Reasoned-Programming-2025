// Klasinn E11 notar klasann Link sem er í Link.java.
// Lesið skilgreiningarnar og setningarnar þar.

// The class E11 uses the class Link in file Link.java.
// Read the definitions and theorems there.

public class E11
{    
    // Notkun: splice(x,i,y);
    // Fyrir:  x er lögleg keðja með N>0 hlekki og hlekkjarunu
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
        // Hér vantar forritstexta með tveimur lykkjum
        // og viðeigandi fastayrðingum. Munið að meðhöndla
        // tilvikið þegar y er tóm keðja.
        // Here we need program text with two loops and
        // appropriate loop invariants.
        // Remember to handle the case when y is empty.
    }
    
    // Notkun: Link<E> x = makeChainLoop(a);
    // Fyrir:  a er E[], ekki null.
    // Eftir:  x er lögleg keðja með N=a.length hlekki og
    //         hlekkjarunu nýrra hlekkja [h_0,...,h_{N-1}] þannig
    //         að h_I.head == a[I] fyrir I=0,...,N-1.
    // Usage:  Link<E> x = makeChainLoop(a);
    // Pre:    a is E[], not null.
    // Post:   x is a legal chain wither N=a.length links and
    //         a sequence [h_0,...,h_{N-1}] of new links such
    //         that h_I.head == a[I] for I=0,...,N-1.
    public static<E> Link<E> makeChainLoop( E[] a )
    {
        // Hér vantar forritstexta sem skal reikna
        // útkomuna í lykkju.
        // Here we need program text that computes
        // the result in a loop.
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
        // Hér vantar forritstexta sem skal reikna
        // útkomuna endurkvæmt.
        // Here we need program text that computes
        // the result recursively.
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