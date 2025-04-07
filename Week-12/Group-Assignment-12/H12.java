// H�fundur: Snorri Agnarsson, snorri@hi.is

// Noti� Link.java, sem er � Canvas, sem hj�lparklasa.

// Visti� �essa skr� undir nafninu H12.java og geri�
// vi�eigandi vi�b�tur �ar sem �i� finni� ???.

// Use Link.java, which is in Canvas, as a helper class.

// In the following discussion all chains are finite
// and legal as described in Link.java.

// Store this file under the name H12.java and make
// the appropriate additions where you find ???

public class H12
{
    // Notkun: split(chain,w);
    // Fyrir:  chain er ke�ja me� a.m.k. tvo hlekki.
    //         w er tveggja staka Link<T>[], �.e. w.length == 2.
    // Eftir:  w[0] og w[1] eru ke�jur sem samanlagt innihalda
    //         hlekkina �r upphaflega chain, � einhverri r��.
    //         Fj�ldi hlekkja � w[0] er anna�hvort sami og � w[1]
    //         e�a einum meiri.
    //         Athugi� a� ekki m� �thluta neinum n�jum hlekkjum
    //         og reyndar ekki neinum n�jum minnissv��um.
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
        // H�r vantar forritstexta.
        // Noti� lykkju.  A�alatri�i� h�r er a� fastayr�ingin
        // lykkjunnar s� g��. Ekki f�st m�rg stig fyrir lausn
        // sem ekki hefur g��a fastayr�ingu jafnvel ��tt
        // falli� virki samkv�mt l�singu.
        // Here we need program text.
        // Use a loop. The most important thing here is that the
        // loop invariant is good. You do not get many point for
        // a solution that does not have a good loop invariant
        // even if the solution works as described.
        ???
    }

    // Notkun: Link<T> y = mergeSort(x,w);
    // Fyrir:  x er l�gleg ke�ja �ar sem hlekkirnir innihalda
    //         l�gleg gildi af tagi T.
    //         w er tveggja staka Link<T>[], �.e. w.length == 2.
    // Eftir:  y er ke�ja s�mu hlekkja �annig a� hlekkirnir
    //         � y eru � vaxandi hausar�� mi�a� vi� compareTo
    //         fyrir hluti af tagi T.
    //         Fylki� w inniheldur engin s�rst�k skilgreind
    //         gildi.
    //         Athugi� a� ekki m� �thluta neinum n�jum hlekkjum
    //         og reyndar ekki neinum n�jum minnissv��um.
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
        // H�r vantar forritstexta.
        // Here we need program text.
        ???
    }
    
    // Notkun: Link<T> z = merge(x,y);
    // Fyrir:  x og y eru ekki-t�mar ke�jur � vaxandi r�� me�
    //         enga sameiginlega hlekki.
    // Eftir:  z er ke�ja � vaxandi r�� sem inniheldur
    //         alla hlekkina �r x og y og enga a�ra.
    //         Athugi� a� ekki m� �thluta neinum n�jum hlekkjum
    //         og reyndar ekki neinum n�jum minnissv��um.
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
        // H�r vantar forritstexta.
        // Noti� lykkju.  A�alatri�i� h�r er a� fastayr�ingin
        // lykkjunnar s� g��. Ekki f�st m�rg stig fyrir lausn
        // sem ekki hefur g��a fastayr�ingu jafnvel ��tt
        // falli� virki samkv�mt l�singu.
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
    // Eftir:  x v�sar � ke�ju n�rra hlekkja sem innihalda
    //         gildin a[i..j), � �eirri r��, sem hausa.
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
    
    // Keyri� skipanirnar
    //   javac H12.java
    //   java H12 1 2 3 4 3 2 1 10 30 20
    // og s�ni� �tkomuna � athugasemd h�r:
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