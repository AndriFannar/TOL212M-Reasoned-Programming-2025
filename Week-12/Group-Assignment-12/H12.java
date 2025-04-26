// Höfundur: Snorri Agnarsson, snorri@hi.is

// Notið Link.java, sem er í Canvas, sem hjálparklasa.

// Vistið þessa skrá undir nafninu H12.java og gerið
// viðeigandi viðbætur þar sem þið finnið ???.

// Use Link.java, which is in Canvas, as a helper class.

// In the following discussion all chains are finite
// and legal as described in Link.java.

// Store this file under the name H12.java and make
// the appropriate additions where you find ???

public class H12
{
    // Notkun: split(chain,w);
    // Fyrir:  chain er keðja með a.m.k. tvo hlekki.
    //         w er tveggja staka Link<T>[], þ.e. w.length == 2.
    // Eftir:  w[0] og w[1] eru keðjur sem samanlagt innihalda
    //         hlekkina úr upphaflega chain, í einhverri röð.
    //         Fjöldi hlekkja í w[0] er annaðhvort sami og í w[1]
    //         eða einum meiri.
    //         Athugið að ekki má úthluta neinum nýjum hlekkjum
    //         og reyndar ekki neinum nýjum minnissvæðum.
    // Usage:  split(chain,w);
    // Pre:    chain is a chain with at least two links.
    //         w is a two element Link<T>[], i.e. w.length == 2.
    // Post:   w[0] and w[1] are chains that together contain
    //         all the links from the original chain, in some order.
    //         The number of links in w[0] is either the same as in
    //         w[1] or one more.
    //         No new links must be allocated and no heap memory
    //         must be allocated.
    public static<T extends Comparable<? super T>>
    void split( Link<T> chain, Link<T>[] w )
    {
        // Hér vantar forritstexta.
        // Notið lykkju.  Aðalatriðið hér er að fastayrðingin
        // lykkjunnar sé góð. Ekki fást mörg stig fyrir lausn
        // sem ekki hefur góða fastayrðingu jafnvel þótt
        // fallið virki samkvæmt lýsingu.
        // Here we need program text.
        // Use a loop. The most important thing here is that the
        // loop invariant is good. You do not get many point for
        // a solution that does not have a good loop invariant
        // even if the solution works as described.
        ???
    }

    // Notkun: Link<T> y = mergeSort(x,w);
    // Fyrir:  x er lögleg keðja þar sem hlekkirnir innihalda
    //         lögleg gildi af tagi T.
    //         w er tveggja staka Link<T>[], þ.e. w.length == 2.
    // Eftir:  y er keðja sömu hlekkja þannig að hlekkirnir
    //         í y eru í vaxandi hausaröð miðað við compareTo
    //         fyrir hluti af tagi T.
    //         Fylkið w inniheldur engin sérstök skilgreind
    //         gildi.
    //         Athugið að ekki má úthluta neinum nýjum hlekkjum
    //         og reyndar ekki neinum nýjum minnissvæðum.
    // Usage:  Link<T> y = mergeSort(x,w);
    // Pre:    x is a legal chain where the links contain legal
    //         objects of type T.
    //         w is a two element Link<T>[], i.e. w.length == 2.
    // Post:   y is a chain of the same links such that the links
    //         are in ascending order of the head values as defined
    //         by compareTo for objects of type T.
    //         The contents of the array w is unspecified.
    //         No new links or other heap objects must be allocated.
    public static<T extends Comparable<? super T>>
    Link<T> mergeSort( Link<T> x, Link<T>[] w )
    {
        // Hér vantar forritstexta.
        // Here we need program text.
        ???
    }
    
    // Notkun: Link<T> z = merge(x,y);
    // Fyrir:  x og y eru ekki-tómar keðjur í vaxandi röð með
    //         enga sameiginlega hlekki.
    // Eftir:  z er keðja í vaxandi röð sem inniheldur
    //         alla hlekkina úr x og y og enga aðra.
    //         Athugið að ekki má úthluta neinum nýjum hlekkjum
    //         og reyndar ekki neinum nýjum minnissvæðum.
    // Usage:  Link<T> z = merge(x,y);
    // Pre:    x and y are non-empty chains in ascending order
	//         with no links in common.
    // Post:   z is a chain in ascending order that contains all
    //         the links from x and y and no others
	//         No new links have been allocated and no heap
	//         memory must be allocated.
    public static<T extends Comparable<? super T>>
    Link<T> merge( Link<T> x, Link<T> y )
    {
        // Hér vantar forritstexta.
        // Notið lykkju.  Aðalatriðið hér er að fastayrðingin
        // lykkjunnar sé góð. Ekki fást mörg stig fyrir lausn
        // sem ekki hefur góða fastayrðingu jafnvel þótt
        // fallið virki samkvæmt lýsingu.
        // Here we need program text.
        // Use a loop. The most important thing here is that the
        // loop invariant is good. You do not get many point for
        // a solution that does not have a good loop invariant
        // even if the solution works as described.
        ???
    }
    
    // Notkun: Link<T> x = makeChain(a,i,j);
    // Fyrir:  a er T[], ekki null.
    //         0 <= i <= j <= a.length.
    // Eftir:  x vísar á keðju nýrra hlekkja sem innihalda
    //         gildin a[i..j), í þeirri röð, sem hausa.
    // Usage:  Link<T> x = makeChain(a,i,j);
    // Pre:    a is a T[], not null.
    //         0 <= i <= j <= a.length.
    // Post:   x refers to a chain of new links that contain
    //         the values a[i..j), in that order, as heads.
    public static<T> Link<T> makeChain( T[] a, int i, int j )
    {
        if( i==j ) return null;
        Link<T> x = new Link<T>();
        x.head = a[i];
        x.tail = makeChain(a,i+1,j);
        return x;
    }
    
    // Keyrið skipanirnar
    //   javac H12.java
    //   java H12 1 2 3 4 3 2 1 10 30 20
    // og sýnið útkomuna í athugasemd hér:
    // Run the commands
    //   javac H12.java
    //   java H12 1 2 3 4 3 2 1 10 30 20
    // and show the results as a comment here:
         ???
    public static void main( String[] args )
    {
        Link<String> x = makeChain(args,0,args.length);
        Link<String>[] w = (Link<String>[])new Link<?>[2];
        x = mergeSort(x,w);
        while( x != null )
        {
            System.out.print(x.head+" ");
            x = x.tail;
        }
    }
}