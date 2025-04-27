// Author: Snorri Agnarsson, snorri@hi.is

// Mutable lists in Java.

// Höfundur: Snorri Agnarsson, snorri@hi.is

// Listar með hliðarverkunum í Java.

public class H9
{
    // Tilvik af link eru breytanlegir hlekkir með
    // haus sem er heiltala og hala sem er endanleg
    // keðja hlekkja.  Tóm keðja er táknuð með null.
    // Það er mögulegt að búa til hringkeðjur og það
    // er mögulegt að breyta bæði haus og hala.
    // Instances of Link are mutable links with a
    // head that is an int and a tail that is a
    // finite chain of links. An empty chain is
    // denoted by null. It is possible to create
    // circular chains and it is possible to change
    // both the head and the tail.
    public static class Link
    {
        public int head;
        public Link tail;
    }
    
    // Notkun: H9.Link x = H9.cons(head,tail);
    // Fyrir:  head er heiltala, tail er H9.Link (má vera null).
    // Eftir:  x er tilvísun á nýjan H9.Link með gefinn haus og
    //         og hala.
    // Usage:  H9.Link x = H9.cons(head,tail);
    // Pre:    head is an int, tail is an E9.Link (may be null).
    // Post:   x refers to a new H9.Link with the given head and
    //         tail.
    public static Link cons( int h, Link t )
    {
        Link newLink = new Link();
        newLink.head = h;
        newLink.tail = t;
        return newLink;
    }
    
    // Notkun: int n = H9.length(x);
    // Fyrir:  x er H9.Link tilvísun, má vera null
    //         en má ekki vísa á hringkeðju.
    // Eftir:  n er fjöldi hlekkja í keðju x.
    // Usage:  int n = H9.length(x);
    // Pre:    x is an H9.Link, may be null,
    //         and must not refer to a circular chain.
    // Eftir:  n is the number of links in the chain x.
    public static int length( H9.Link x )
    {
        int n = 0;
        Link z = x;
        while( z != null )
            // z er aftari hluti keðju x.
            // n er fjöldi hlekkja í x fyrir framan z.
            // z is a suffix of the chain x.
            // There are n links in x in front of z.
        {
            n++;
            z = z.tail;
        }
        return n;
    }

    // Notkun: int i = H9.nth(x,n);
    // Fyrir:  x er keðja með a.m.k. n+1 hlekki.
    // Eftir:  i er hausinn á n-ta hlekk í keðjunni
    //         þar sem 0-ti hlekkur er fremsti hlekkur.
    // Usage:  int i = H9.nth(x,n);
    // Pre:    n>=0, x is a chain with at least n+1 links.
    // Post:   i is the head of the n-th link in the chain
    //         where the 0-th link is the first link.
    public static int nth( H9.Link x, int n )
    {
        int i = 0;
        Link z = x;
        while( i != n )
            // z er aftari hluti keðju x.
            // i er fjöldi hlekkja í x sem ekki eru í z.
            // z is a suffix of the chain x.
            // There are i links in x that are not in z.
        {
            i++;
            z = z.tail;
        }
        return z.head;
    }
    
    // Notkun: H9.Link x = makeChain(a);
    // Fyrir:  a er tilvísun á int[]. Má ekki vera null
    //         en má vera tómt.
    // Eftir:  x er keðja nýrra hlekkja sem inniheldur gildin í a
    //         þannig að fyrir i=0,...,a.length gildir
    //         H9.nth(x,i) == a[i].
    // Usage:  H9.Link x = H9.makeChain(a);
    // Pre:    a refers to an int[]. Must not be null,
    //         but may be empty.
    // Post:   x is a chain that contains the values in a
    //         such that for i=0,...,a.length-1 we have
    //         H9.nth(x,i) == a[i].
    public static Link makeChain( int[] a )
    {
        int i = a.length;
        Link z = null;
        while( i != 0 )
            // z er keðja nýrra hlekkja sem inniheldur a[i..a.length),
            // í þeirri röð.
            // 0 <= i <= a.length.
            // z is a chain of new links that contains a[i..a.length),
            // in that order.
        {
            i--;
            Link tmp = new Link();
            tmp.head = a[i];
            tmp.tail = z;
            z = tmp;
        }
        return z;
    }
    
    // Notkun: int i = H9.last(x);
    // Fyrir:  x er tilvísun á H9.Link, má ekki vera null
    //         og má ekki vera hringkeðja.
    // Eftir:  i er gildið í (hausinn á) aftasta hlekk x.
    // Usage:  int i = H9.last(x);
    // Pre:    x refers to a H9.Link, must not be null,
    //         and must not refer to a circular chain.
    // Post:   i is the value in (the head of) the last
    //         link in x.
    public static int last( Link x )
    {
        Link z = x;
        while( z.tail != null )
            // z er aftari hluti keðju x, z != null.
            // z is a suffix of the chain x, z != null.
        {
            z = z.tail;
        }
        return z.head;
    }

    // Notkun: H9.Link z = H9.destructiveRemoveLast(x);
    // Fyrir:  x er tilvísun á H9.Link, má ekki vera null
    //         og má ekki vera hringkeðja.
    // Eftir:  z er keðja sem inniheldur sömu hlekki í
    //         sömu röð og x, nema hvað hlekkurinn sem
    //         var aftast er ekki lengur í keðjunni og
    //         í stað tilvísunar á þann hlekk inniheldur nú
    //         aftasti hlekkurinn hala sem er null.
    //         Eftir kallið eru sömu heiltölugildi í
    //         hlekkjunum og sömu halar, fyrir utan í
    //         hlekknum sem nú er aftast (ef einhver er).
    //         Gilda þarf að E9.length(z) == gamla(E9.length(x))-1
    //         og fyrir i=0,...,E9.length(z)-1 þarf að gilda
    //         E9.nth(z,i) == gamla(E9.nth(x,i)).
    // Usage:  H9.Link z = H9.destructiveRemoveLast(x);
    // Pre:    x refers to an H9.Link, must not be null
    //         and must not be circular.
    // Post:   z is a chain that contains the same links
    //         in the same order as x, except that the
    //         link that was last in x has been removed.
    //         The link in x that was in front of that
    //         last link (if any) now has a tail that is
    //         null.
    public static Link destructiveRemoveLast( Link x )
    {
        if( x.tail == null ) return null;
        Link z = x;
        while( z.tail.tail != null )
            // z er aftari hluti keðju x og inniheldur
            // a.m.k. tvo hlekki, þ.e. z.tail er ekki null.
            // z is a suffix of the chain x and contains
            // at least two links, i.e. z.tail is not null.
        {
            z = z.tail;
        }
        z.tail = null;
        return x;
    }
    
    // Notkun: H9.Link r = H9.destructiveReverse(x);
    // Fyrir:  x er keðja, má vera tóm.
    // Eftir:  z er keðja sömu hlekkja og x, þannig að
    //         hlekkirnir í r eru í öfugri röð miðað
    //         við gamla x. Heiltölugildin í hlekkjunum
    //         eru óbreytt.
    // Usage:  H9.Link r = H9.destructiveReverse(x);
    // Pre:    x is a chain, mey be empty.
    // Post:   z is a chain containing the same links as
    //         x, but the order of the links has been
    //         reversed. The int values in the links are
    //         unchanged.
    public static Link destructiveReverse( Link x )
    {
        Link res = null;
        Link rest = x;
        while( rest != null )
            // res er viðsnúin keðja núll eða fleiri
            // fremstu hlekkja upphaflega x. rest er
            // aftari hluti upphaflega x sem eftir er
            // að snúa.
            // res is a reversed chain of zero or more
            // frontmost links from the original x.
            // rest is a suffix of the original x that
            // is yet to be reversed.
        {
            Link tmp = rest.tail;
            rest.tail = res;
            res = rest;
            rest = tmp;
        }
        return res;
    }
    
    public static void main( String[] args )
    {
        H9.Link x = null;
        for( int i=0 ; i!=args.length ; i++ )
            x = H9.cons(Integer.parseInt(args[i]),x);
        while( x != null )
        {
            H9.Link z = H9.destructiveReverse(x);
            x = z;
            while( z != null )
            {
                System.out.print(z.head); System.out.print(" ");
                z = z.tail;
            }
            x = H9.destructiveRemoveLast(x);
            System.out.println();
        }
    }
}