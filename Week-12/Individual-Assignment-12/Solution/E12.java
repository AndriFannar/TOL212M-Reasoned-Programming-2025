// H�fundur: Snorri Agnarsson, snorri@hi.is

// Noti� Link.java, sem er � Canvas, sem hj�lparklasa.

// � eftirfarandi umfj�llun eru allar ke�jur endanlegar
// og l�glegar eins og l�st er � Link.java

// Use Link.java, which is in Canvas, as a helper class.

// In the following discussion all chains are finite
// and legal as described in Link.java.

// Store this file under the name E12.java and make
// the appropriate additions where you find ???

public class E12
{
    // Notkun: removeMinLink(chain,res);
    // Fyrir:  chain er ekki-t�m ke�ja.
    //         res er tveggja staka Link<T>[], �.e. res.length == 2.
    // Eftir:  res[0] v�sar � �ann hlekk innan gamla chain sem
    //         inniheldur minnsta gildi�.
    //         res[1] v�sar � ke�ju hinna hlekkjanna sem voru �
    //         gamla chain, � einhverri �skilgreindri r��.
    //         Allir hlekkir � gamla chain eru anna� hvort � ke�junni
    //         res[1] e�a eru hlekkurinn sem res[0] v�sar �.
    //         Ekki �arf a� taka fram (� Java) a� �ll gildi (head) �
    //         hlekkjunum eru �breytt, a�eins halarnir (tail) hafa
    //         hugsanlega breyst.
    //         Ekki m� �thluta neinum n�jum hlekkjum.
    // Ath.:   B�a m� til fylki res me� eftirfarandi Java skipun:
    //           Link<T>[] res = (Link<T>[])new Link<?>[2];
    //         �i� f�i� �� a�v�run fr� Java, en �a� er � lagi.
    // Usage:  removeMinLink(chain,res);
    // Pre:    chain is a non-empty chain.
    //         res is a two element Link<T>[], i.e. res.length == 2.
    // Post:   res[0] refers to the link in the original chain which
    //         contains the smallest value.
    //         res[1] refers to a chain containing all the other links
    //         which were in chain in some unspecified order.
    //         All the links that originally were in chain are either
    //         in the chain res[1] or are the link that res[0] refers
    //         to. All the values (heads) in the links are unchanged,
    //         only the tails hae changed. No new links have been
    //         allocated.
    // Note:   The array res can be allocated using the following statement:
    //           Link<T>[] res = (Link<T>[])new Link<?>[2];
    //         You will get a warning from Java, but that is normal.
    public static<T extends Comparable<? super T>>
    void removeMinLink( Link<T> chain, Link<T>[] res )
    {
        Link<T> min = chain;
        Link<T> rest = chain.tail;
        Link<T> discarded = null;
        while( rest != null )
            // min v�sar � hlekk � upphaflegu chain ke�junni.
            // rest og discarded eru (l�glegar) ke�jur.
            // Hlekkirnir � rest og discarded, auk hlekksins
            // sem min v�sar � eru samtals allir hlekkir �
            // upphaflegu chain ke�junni.
            // �ll gildi � hlekkjunum � ke�junni discarded
            // eru >= gildi� � hlekknum min.
            // ��arfi er a� taka fram a� �ll gildi (hausar)
            // � �llum hlekkjum eru �breytt.
            // min refers to a link in the original chain.
            // rest and discarded are (legal) chains.
            // The links in rest and discarded, along with
            // the link that min refers to, are in total all
            // the links in the original chain.
            // All the values in the discarded chain are >=
            // the value in the min link. No values in any
            // link has been modified (don't need to state that).
        {
            Link<T> tmp = rest.tail;
            if( rest.head.compareTo(min.head) < 0 )
            {
                min.tail = discarded;
                discarded = min;
                min = rest;
            }
            else
            {
                rest.tail = discarded;
                discarded = rest;
            }
            rest = tmp;
        }
        res[0] = min;
        res[1] = discarded;
    }

    // Notkun: Link<T> y = selectionSort(x);
    // Fyrir:  x er l�gleg ke�ja �ar sem hlekkirnir innihalda
    //         l�gleg gildi af tagi T.
    // Eftir:  y er ke�ja s�mu hlekkja �annig a� hlekkirnir
    //         � y eru � vaxandi hausar�� mi�a� vi� compareTo
    //         fyrir hluti af tagi T.
    // Usage:  Link<T> y = selectionSort(x);
    // Pre:    x is a legal chain where the links contain legal
    //         objects of type T.
    // Post:   y is a chain of the same links such that the links
    //         are in ascending order of the head values as defined
    //         by compareTo for objects of type T.
    public static<T extends Comparable<? super T>>
    Link<T> selectionSort( Link<T> x )
    {
        if( x == null ) return null;
        Link<T>[] res = (Link<T>[])new Link<?>[2];
        removeMinLink(x,res);
        Link<T> firstInResult = res[0];
        Link<T> lastInResult = firstInResult;
        Link<T> rest = res[1];
        while( rest != null )
            // rest er ke�ja hlekkja sem allir eru �r upphaflegu
            // x ke�junni.
            // firstInResult og lastInResult v�sa � hlekki sem
            // einnig eru �r upphaflegu x ke�junni (g�ti veri�
            // sami hlekkur).
            // lastInResult.tail inniheldur ekkert skilgreint
            // gildi, en ef lastInResult.tail v�ri sett sem null
            // �� v�ri firstInResult l�gleg ke�ja me� lastInResult
            // sem aftasta hlekk. Gildin � �eirri ke�ju eru �
            // vaxandi r�� og eru �ll <= �ll gildi � rest.
            // Samtals inniheldur s� (�mynda�a) firstInResult
            // ke�ja, auk ke�junnar rest, alla hlekkina �r
            // upphaflega x og enga a�ra hlekki.  Ke�jan rest
            // og firstInResult ke�jan (me� lastInRest.tail==null)
            // hafa enga sameiginlega hlekki.
            // rest is a chain of links that are all from the original
            // x chain.
            // firstInResult and lastInResult refer to links that
            // also are from the original x chain (could be the same link).
            // lastInResult.tail contains an unspecified value, but
            // if lastInResult.tail was set as null then firstInResult
            // would be a legal chain with lastInResult
            // as the last link. The values in that chain are in
            // ascending order and are all <= all values in rest.
            // The total contents of the (imaginary) firstInResult
            // chain, plus chain rest, are all the links from the
            // original x and no other links. The rest chain
            // and the firstInResult chain (with lastInRest.tail==null)
            // have no common links.
        {
            removeMinLink(rest,res);
            rest = res[1];
            lastInResult.tail = res[0];
            lastInResult = lastInResult.tail;
        }
        lastInResult.tail = null;
        return firstInResult;
    }
    
    // Notkun: Link<T> z = insert(x,y);
    // Fyrir:  x er ke�ja � vaxandi r�� (m� vera t�m).
    //         y v�sar � hlekk (m� ekki vera null).
    // Eftir:  z er ke�ja � vaxandi r�� sem inniheldur
    //         alla hlekkina �r x auk hlekksins y.
    //         Athugi� a� ekki m� �thluta neinum n�jum
    //         hlekkjum.
    // Usage:  Link<T> z = insert(x,y);
    // Pre:    x is a chain in ascending order (may be empty).
    //         y refers to a link (must not be null).
    // Post:   z is a chain in ascending order that contains
    //         all the links from x and also the link y.
    //         No new links must be allocated.
    public static<T extends Comparable<? super T>>
    Link<T> insert( Link<T> x, Link<T> y )
    {
        if( x == null || y.head.compareTo(x.head) <= 0 )
        {
            y.tail = x;
            return y;
        }
        Link<T> lastKnownLT = x;
        while( lastKnownLT.tail != null && lastKnownLT.tail.head.compareTo(y.head) < 0 )
            // Ke�jan x er �breytt og lastKnownLT v�sar � hlekk � x sem inniheldur gildi
            // sem er < y.head.
            // �arme� innihalda allir hlekkir �ar fyrir framan einnig gildi < y.head.
			// The chain x is unchanged and lastKnownLT refers to a link in x that
			// contains a value < y.head.
			// Thereby all the links in front of that link also contain values
			// that are < y.head.
        {
            lastKnownLT = lastKnownLT.tail;
        }
        y.tail = lastKnownLT.tail;
        lastKnownLT.tail = y;
        return x;
    }

    
    // Notkun: Link<T> y = insertionSort(x);
    // Fyrir:  x er l�gleg ke�ja �ar sem hlekkirnir innihalda
    //         l�gleg gildi af tagi T.
    // Eftir:  y er ke�ja s�mu hlekkja �annig a� hlekkirnir
    //         � y eru � vaxandi hausar�� mi�a� vi� compareTo
    //         fyrir hluti af tagi T.
    // Usage:  Link<T> y = insertionSort(x);
    // Pre:    x is a legal chain where the links contain legal
    //         objects of type T.
    // Post:   y is a chain of the same links such that the links
    //         are in ascending order of the head values as defined
    //         by compareTo for objects of type T.
    public static<T extends Comparable<? super T>>
    Link<T> insertionSort( Link<T> x )
    {
        Link<T> res = null;
        while( x != null )
            // res inniheldur n�ll e�a fleiri hlekki �r upphaflega x � vaxandi r��.
            // x inniheldur restina af hlekkjunum �r upphaflega x � einhverri r��.
			// res contains zero or more links from the original x in ascending order.
			// x contains the rest of the links from the original x in some order.
        {
            Link<T> linkToInsert = x;
            x = x.tail;
            res = insert(res,linkToInsert);
        }
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
    //   javac E12.java
    //   java E12 1 2 3 4 3 2 1 10 30 20
    // og s�ni� �tkomuna � athugasemd h�r:
    // Run the commands
    //   javac E12.java
    //   java E12 1 2 3 4 3 2 1 10 30 20
    // and show the results as a comment here:
    //    1 1 10 2 2 20 3 3 30 4
    //    1 1 10 2 2 20 3 3 30 4
    public static void main( String[] args )
    {
        Link<String> x = makeChain(args,0,args.length);
        x = selectionSort(x);
        while( x != null )
        {
            System.out.print(x.head+" ");
            x = x.tail;
        }
        System.out.println();
        x = makeChain(args,0,args.length);
        x = insertionSort(x);
        while( x != null )
        {
            System.out.print(x.head+" ");
            x = x.tail;
        }
    }
}