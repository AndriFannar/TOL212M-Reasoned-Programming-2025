// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

// Notið Link.java, sem er í Canvas, sem hjálparklasa.

// Í eftirfarandi umfjöllun eru allar keðjur endanlegar
// og löglegar eins og lýst er í Link.java

// Vistið þessa skrá undir nafninu E12.java og gerið
// viðeigandi viðbætur þar sem þið finnið ???

// Use Link.java, which is in Canvas, as a helper class.

// In the following discussion all chains are finite
// and legal as described in Link.java.

// Store this file under the name E12.java and make
// the appropriate additions where you find ???

public class E12
{
    // Notkun: removeMinLink(chain,res);
    // Fyrir:  chain er ekki-tóm keðja.
    //         res er tveggja staka Link<T>[], þ.e. res.length == 2.
    // Eftir:  res[0] vísar á þann hlekk innan gamla chain sem
    //         inniheldur minnsta gildið.
    //         res[1] vísar á keðju hinna hlekkjanna sem voru í
    //         gamla chain, í einhverri óskilgreindri röð.
    //         Allir hlekkir í gamla chain eru annað hvort í keðjunni
    //         res[1] eða eru hlekkurinn sem res[0] vísar á.
    //         Ekki þarf að taka fram (í Java) að öll gildi (head) í
    //         hlekkjunum eru óbreytt, aðeins halarnir (tail) hafa
    //         hugsanlega breyst.
    //         Ekki má úthluta neinum nýjum hlekkjum.
    // Ath.:   Búa má til fylki res með eftirfarandi Java skipun:
    //           Link<T>[] res = (Link<T>[])new Link<?>[2];
    //         Þið fáið þá aðvörun frá Java, en það er í lagi.
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
        // Hér vantar forritstexta.
        // Útfærið þetta með lykkju þar sem fastayrðingin skal
        // vera keimlík þeirri fastayrðingu sem notuð var í
        // lausninni á MinOfMultiset sem við leystum áður í
        // Dafny.  Aðalatriðið hér er að fastayrðingin
        // lykkjunnar sé góð. Ekki fást mörg stig fyrir lausn
        // sem ekki hefur góða fastayrðingu jafnvel þótt
        // fallið virki samkvæmt lýsingu.
        // Here we need program text.
        // Implement this with a loop where the loop invariant
        // will be similar to the one in the Dafny method
        // MinOfMultiset that we implemented earlier. The
        // most important thing here is that the loop
        // invariant is good. You do not get many point for
        // a solution that does not have a good loop invariant
        // even if the solution works as described.
        ???
    }

    // Notkun: Link<T> y = selectionSort(x);
    // Fyrir:  x er lögleg keðja þar sem hlekkirnir innihalda
    //         lögleg gildi af tagi T.
    // Eftir:  y er keðja sömu hlekkja þannig að hlekkirnir
    //         í y eru í vaxandi hausaröð miðað við compareTo
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
        // Hér vantar forritstexta.
        // Útfærið þetta með lykkju þar sem fastayrðingin skal
        // vera keimlík þeirri fastayrðingu sem notuð var í
        // lausninni á Sort í E3.dfy sem við leystum áður í
        // Dafny.  Aðalatriðið hér er að fastayrðingin
        // lykkjunnar sé góð. Ekki fást mörg stig fyrir lausn
        // sem ekki hefur góða fastayrðingu jafnvel þótt
        // fallið virki samkvæmt lýsingu.
        // Here we need program text.
        // Implement this with a loop where the loop invariant
        // will be similar to the one in the Dafny method
        // Sort in E3.dfy that we implemented earlier. The
        // most important thing here is that the loop
        // invariant is good. You do not get many point for
        // a solution that does not have a good loop invariant
        // even if the solution works as described.
        ???
    }
    
    // Notkun: Link<T> z = insert(x,y);
    // Fyrir:  x er keðja í vaxandi röð (má vera tóm).
    //         y vísar á hlekk (má ekki vera null).
    // Eftir:  z er keðja í vaxandi röð sem inniheldur
    //         alla hlekkina úr x auk hlekksins y.
    //         Athugið að ekki má úthluta neinum nýjum
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
        // Hér vantar forritstexta.
        // Here we need program text.
        ???
    }

    
    // Notkun: Link<T> y = insertionSort(x);
    // Fyrir:  x er lögleg keðja þar sem hlekkirnir innihalda
    //         lögleg gildi af tagi T.
    // Eftir:  y er keðja sömu hlekkja þannig að hlekkirnir
    //         í y eru í vaxandi hausaröð miðað við compareTo
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
        // Hér vantar forritstexta.
        // Here we need program text.
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
    //   javac E12.java
    //   java E12 1 2 3 4 3 2 1 10 30 20
    // og sýnið útkomuna í athugasemd hér:
    // Run the commands
    //   javac E12.java
    //   java E12 1 2 3 4 3 2 1 10 30 20
    // and show the results as a comment here:
        ???
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