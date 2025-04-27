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
        /*
        // A solution using a simple loop invariant
        Link<T> x = null;
        Link<T> y = null;
        Link<T> rest = chain;
        for(;;)
        {
            // x,y og rest eru ke�jur sem samanlagt innihalda
            // hlekkina �r upphaflega chain.
            // Ke�jurnar x og y eru jafn langar.
            // x,y and rest are chains that together contain
            // the links from original chain.
            // x and y are of equal lengths.
            if( rest == null ) break;
            Link<T> tmp = rest.tail;
            rest.tail = x;
            x = rest;
            rest = tmp;
            if( rest == null ) break;
            tmp = rest.tail;
            rest.tail = y;
            y = rest;
            rest = tmp;
        }
        w[0] = x;
        w[1] = y;
        */

        /*
        // Another (faster) solution using the loop invariant from our slides
        if( chain.tail.tail == null )
        {
            w[0] = chain;
            w[1] = chain.tail;
            chain.tail = null;
            return;
        }
        Link<T> x = chain;
        Link<T> y = x;
        Link<T> z = x.tail.tail;
        while( z!=null && z.tail!=null )
        {
            // x is a non-empty chain of n links with values
            // v_0,v_1,...,v_{n-1}, same as chain, and we wish
            // to split it into two halves.
            // y is some non-empty suffix of x and the number
            // of links from x to y inclusive is i, for some i.
            // z is some suffix of y and the number of links
            // in x following y and up to but not including z
            // is also i.
            z = z.tail.tail;
            y = y.tail;
        }
        w[0] = y.tail;
        y.tail = null;
        w[1] = x;
        */
        
        // A recursive solution. Perhaps the simplest solution
        // unless we change the preconditions to allow chain==null
        // or chain.tail==null.
        if( chain.tail.tail == null || chain.tail.tail.tail==null )
        {
            w[1] = chain;
            w[0] = chain.tail;
            chain.tail = null;
            return;
        }
        Link<T> link0 = chain;
        Link<T> link1 = chain.tail;
        split(chain.tail.tail,w);
        link0.tail = w[0];
        link1.tail = w[1];
        w[0] = link0;
        w[1] = link1;
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
        if( x == null || x.tail == null ) return x;
        split(x,w);
        Link<T> y = w[0];
        Link<T> z = w[1];
        y = mergeSort(y,w);
        z = mergeSort(z,w);
        return merge(y,z);
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
        Link<T> res, last;
        if( x.head.compareTo(y.head) < 0 )
        {
            res = x;
            last = x;
            x = x.tail;
        }
        else
        {
            res = y;
            last = y;
            y = y.tail;
        }
        while( x != null && y != null )
            // last.tail inniheldur ekkert skilgreint
            // gildi, en ef last.tail v�ri null �� v�ri
            // res ekki-t�m ke�ja me� hlekkinn last sem
            // s��asta hlekk.  Hlekkirnir � �eirri ke�ju,
            // auk hlekkjanna � ke�junum x og y, eru
            // samtals s�mu hlekkir og voru samtals �
            // upphaflegu ke�junum x og y.  Allir
            // hlekkirnir � res innihalda gildi
            // sem eru <= �ll gildi � x og y og eru �
            // vaxandi r��. Hlekkirnir � x og y eru
            // einnig � vaxandi r��.
            // The value in last.tail is unspecified, but
            // if it were set to null then res would be a
            // non-empty chain with the link last a the
            // last link. The links in that chain along
            // with the links in the chains x and y are
            // all the links that were originally in x
            // and y. All the links in res contain values
            // that are <= all the values in x and y, and
            // they are in ascending order. The chains x
            // and y are also in ascending order.
        {
            if( x.head.compareTo(y.head) < 0 )
            {
                last.tail = x;
                last = x;
                x = x.tail;
            }
            else
            {
                last.tail = y;
                last = y;
                y = y.tail;
            }            
        }
        last.tail = x==null ? y : x;
        return res;
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
    //     1 1 10 2 2 20 3 3 30 4
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