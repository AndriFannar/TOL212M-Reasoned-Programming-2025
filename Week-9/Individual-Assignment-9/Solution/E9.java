// H�fundur: Snorri Agnarsson, snorri@hi.is

// Listar �n hli�arverkana � Java.

public class E9
{
    // Tilvik af link eru �breytanlegir hlekkir me�
    // haus sem er heiltala og hala sem er endanleg
    // ke�ja hlekkja.  Taki� eftir a� �a� er enginn
    // m�guleiki � a� breyta halanum og �v� eru allar
    // ke�jur endanlegar.  T�m ke�ja er t�knu� me� null.
    // Instances of Link are immutable links with a
    // head that is an integer and a tail that is a
    // finite chain of links. Note that there is no
    // possibility to change the tail and therefore
    // al chains are finite. An empty chain is denoted
    // by null.
    public static class Link
    {
        private final int head;
        private final Link tail;
        
        // Notkun: E9.Link x = new E9.Link(head,tail);
        // Fyrir:  head er heiltala, tail er E9.Link (m� vera null).
        // Eftir:  x er tilv�sun � n�jan E9.Link me� gefinn haus og
        //         og hala.
        // Usage:  E9.Link x = new E9.Link(head,tail);
        // Pre:    head is an int, tail is an E9.Link (may be null).
        // Post:   x refers to a new E9.Link with the given head and
        //         tail.
        public Link( int head, Link tail )
        {
            this.head = head;
            this.tail = tail;
        }
        
        // Notkun: int h = link.head();
        // Fyrir:  link v�sar � E9.Link.
        // Eftir:  h er hausinn � link.
        // Usage:  int h = link.head();
        // Pre:    link refers to an E9.Link object.
        // Post:   h contains the head of link.
        public int head()
        {
            return head;
        }
        
        // Notkun: E9.Link t = link.tail();
        // Fyrir:  link v�sar � E9.Link.
        // Eftir:  t er halinn � link.
        // Usage:  E9.Link t = link.tail();
        // Pre:    link refers to an E9.Link object.
        // Post:   t contains the tail of link.
        public Link tail()
        {
            return tail;
        }
    }
    
    // Notkun: E9.Link x = E9.cons(head,tail);
    // Fyrir:  head er heiltala, tail er E9.Link (m� vera null).
    // Eftir:  x er tilv�sun � n�jan E9.Link me� gefinn haus og
    //         og hala.
    // Usage:  E9.Link x = E9.cons(head,tail);
    // Pre:    head is an int, tail is an E9.Link (may be null).
    // Post:   x refers to a new E9.Link with the given head and
    //         tail.
    public static Link cons( int h, Link t )
    {
        return new Link(h,t);
    }
    
    // Notkun: int h = head(x);
    // Fyrir:  x er tilv�sun � E9.Link, m� ekki vera null.
    // Eftir:  h er hausinn � x.
    // Usage:  int h = E9.head(x);
    // Pre:    link refers to an E9.Link object.
    // Post:   h contains the head of x.
    public static int head( Link x )
    {
        return x.head();
    }
    
    // Notkun: E9.Link t = tail(x);
    // Fyrir:  x er tilv�sun � E9.Link, m� ekki vera null.
    // Eftir:  h er halinn � x.
    // Usage:  E9.Link t = tail(x);
    // Pre:    x refers to an E9.Link object.
    // Post:   t contains the tail of x.
    public static Link tail( Link x )
    {
        return x.tail();
    }
        
    // Notkun: int n = E9.length(x);
    // Fyrir:  x er E9.Link tilv�sun, m� vera null.
    // Eftir:  n er fj�ldi hlekkja � ke�ju x.
    // Usage:  int n = E9.length(x);
    // Pre:    x is an E9.Link, may be null.
    // Eftir:  n is the number of links in the chain x.
    public static int length( E9.Link x )
    {
        int n = 0;
        Link z = x;
        while( z != null )
            // z er aftari hluti ke�junnar x.
            // Hlekkirnir � x sem ekki eru � z
            // eru n talsins.
            // z is a suffix of the chain x.
            // There are n links in x that
            // are not in z.
        {
            n++;
            z = tail(z);
        }
        return n;
    }

    // Notkun: int i = E9.nth(x,n);
    // Fyrir:  x er ke�ja me� a.m.k. n+1 hlekki.
    // Eftir:  i er hausinn � n-ta hlekk � ke�junni
    //         �ar sem 0-ti hlekkur er fremsti hlekkur.
    // Usage:  int i = E9.nth(x,n);
    // Pre:    n>=0, x is a chain with at least n+1 links.
    // Post:   i is the head of the n-th link in the chain
    //         where the 0-th link is the first link.
    public static int nth( E9.Link x, int n )
    {
        int i = 0;
        Link z = x;
        while( i != n )
            // z er aftari hluti ke�junnar x.
            // Hlekkirnir � x sem ekki eru � z
            // eru i talsins.
            // z is a suffix of the chain x.
            // There are i links in x that are
            // not in z.
        {
            i++;
            z = tail(z);
        }
        return head(z);
    }
    
    // Notkun: E9.Link x = makeChain(a);
    // Fyrir:  a er tilv�sun � int[]. M� ekki vera null
    //         en m� vera t�mt.
    // Eftir:  x er ke�ja n�rra hlekkja sem inniheldur gildin � a
    //         �annig a� fyrir i=0,...,a.length gildir
    //         E9.nth(x,i) == a[i].
    // Usage:  E9.Link x = makeChain(a);
    // Pre:    a refers to an int[]. Must not be null,
    //         but may be empty.
    // Post:   x is a chain that contains the values in a
    //         such that for i=0,...,a.length-1 we have
    //         E9.nth(x,i) == a[i].
    public static Link makeChain( int[] a )
    {
        int i = a.length;
        Link z = null;
        while( i != 0 )
            // z er ke�ja n�rra hlekkja sem inniheldur a[i..a.length),
            // � �eirri r��.
            // 0 <= i <= a.length.
            // z is a chain of new links that contains a[i..a.length),
            // in that order.
        {
            i--;
            z = cons(a[i],z);
        }
        return z;
    }
    
    // Notkun: int i = E9.last(x);
    // Fyrir:  x er tilv�sun � E9.Link, m� ekki vera null.
    // Eftir:  i er gildi� � (hausinn �) aftasta hlekk x.
    // Usage:  int i = E9.last(x);
    // Pre:    x refers to a E9.Link, must not be null.
    // Post:   i is the value in (the head of) the last
    //         link in x.
    public static int last( Link x )
    {
        Link z = x;
        while( tail(z) != null )
            // z er aftari hluti ke�ju x.
            // z er ekki null.
            // z is a suffix of the chain x.
            // z is not null.
        {
            z = tail(z);
        }
        return head(z);
    }

    // Notkun: E9.Link z = E9.removeLast(x);
    // Fyrir:  x er tilv�sun � E9.Link, m� ekki vera null.
    // Eftir:  z er ke�ja sem inniheldur n�ja hlekki
    //         �annig a� E9.length(z) == E9.length(x)-1
    //         og fyrir i=0,...,E9.length(z)-1 gildir
    //         E9.nth(z,i) == E9.nth(z,i).
    // Usage:  E9.Link z = E9.removeLast(x);
    // Pre:    x refers to a E9.Link, must not be null.
    // Post:   z is a chain of new links such that
    //         E9.length(z) == E9.length(x)-1
    //         and for i=0,...,E9.length(z)-1 we have
    //         E9.nth(z,i) == E9.nth(x,i).
    public static Link removeLast( Link x )
    {
        Link z = null;
        Link w = x;
        while( tail(w) != null )
            // w er aftari hluti ke�junnar x, ekki t�mur.
            // z er ke�ja n�rra hlekkja sem inniheldur s�mu gildin
            // og �eir hlekkir x sem ekki eru � w, � �fugri r��
            // mi�a� vi� r��ina � x.
            // w is a suffix of the chain x, not empty.
            // z is a chain of new links that contains the same
            // values as the links in x that are not in w, in the
            // reverse order of the order in x.
        {
            z = cons(head(w),z);
            w = tail(w);
        }
        return reverse(z);
        
        /*
        // Einnig m� skrifa �tg�fu me� einni lykku �n kalls �
        // reverse sem hefur t�mafl�kju O(n^2):
        Link z = null;
        int i = 0, n = E9.length(x);
        while( i != n-1 )
            // n er fj�ldi hlekkja � x.
            // 0 <= i <= n-1.
            // z er ke�ja n�rra hlekkja af lengd i sem inniheldur
            // s�mu gildi � s�mu r�� og n�st�ftustu hlekkirnir
            // � x. Me� ��rum or�um gildir fyrir j �.a. 0 <= j < i
            // a� E9.nth(w,j) == E9.nth(x,n-j-i-1).
            // Ef vi� notum svipa�an rith�tt fyrir sv��i � ke�ju og
            // nota m� � Dafny �� getum vi� skrifa�
            //        0 <= i <= n-1
            //        |ListSeq(z)| == i
            //        |ListSeq(x)| == n
            //        ListSeq(z) == ListSeq(x)[n-i-1..n-1)
        {
            i = i+1;
            z = E9.cons(E9.nth(x,n-i-1),z);
        }
        return z;
        */
        
        /*
        // Ef ekki hef�i veri� krafa um a� ekki m�tti nota
        // endurkv�mni, g�tum vi� skrifa� lausnina svona:
        if( E9.tail(x) == null ) { return null; }
        return E9.cons(E9.head(x),E9.removeLast(E9.tail(x)));
        */
    }
    
    // Notkun: E9.Link r = E9.reverse(x);
    // Fyrir:  x er ke�ja, m� vera t�m.
    // Eftir:  z er jafn l�ng ke�ja og x, �annig a�
    //         fyrir i=0,...,E9.length(x)-1 gildir
    //         E9.nth(x,i) == E9.nth(r,E9.length(x)-i-1).
    // Usage:  E9.Link r = E9.reverse(x);
    // Pre:    x is a chain, may be empty.
    // Post:   z is a new chain of equal length to x, such
    //         that for i=0,...,E9.length(x)-1 we have
    //         E9.nth(x,i) == E9.nth(r,E9.length(x)-i-1).
    public static Link reverse( Link x )
    {
        Link res = null;
        Link z = x;
        while( z != null )
            // z er aftari hluti ke�junnar x.
            // res er ke�ja n�rra hlekkja sem inniheldur
            // s�mu gildi og �eir hlekkir x sem ekki eru
            // � z, en � �fugri r��.
            // z is a suffix of the chain x.
            // res is a chain of new links that contains
            // the same values as the links in x that are
            // not in z, but in the reverse order.
        {
            res = cons(head(z),res);
            z = tail(z);
        }
        return res;
    }
   
    public static void main( String[] args )
    {
        E9.Link x = null;
        for( int i=0 ; i!=args.length ; i++ )
            x = E9.cons(Integer.parseInt(args[i]),x);
        while( x != null )
        {
            E9.Link z = reverse(x);
            x = z;
            while( z != null )
            {
                System.out.print(z.head); System.out.print(" ");
                z = z.tail;
            }
            x = E9.removeLast(x);
            System.out.println();
        }
    }
}