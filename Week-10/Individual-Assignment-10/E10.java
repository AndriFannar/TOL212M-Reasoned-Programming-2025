// Tilvik af E10<T> eru biðraðir gilda af tagi T.
// Instances of E10<T> are queues of values of type T.
public class E10<T>
{
    static class Link<E>
    {
        public E head;
        public Link<E> tail;
    }
    
    // Athugið: Búa má til nýjan hlekk fyrir gildi
    // af tagi T svona:
    // Note: new links for values of type T can
    // be created like this:
    //    Link<T> x = new Link<T>();
    
    Link<T> last;
    
    /* Fastayrðing gagna:
        Skrifið hér fastayrðingu gagna á íslensku
        eða ensku, sem samsvarar fastayrðingunni
        (þ.e. umsögninni Valid()) í Dafny skránni
        H10.dfy.  Reynið að vera stuttorð og nákvæm.
        Nauðsynlegt er að fastayrðingin sé sönn
        eftir smíð hlutar af tagi E10<T> og gefi
        nægilegar upplýsingar til að forritari geti
        útfært smiðinn fyrir E10 og sérhverja af
        aðgerðunum isEmpty(), put(x) og get() án
        þess að vita innviði hinna aðgerðanna.
        Einu nauðsynlegu upplýsingarnar fyrir
        forritara til að útfæra hverja af
        aðgerðunum eru fastayrðing gagna og
        lýsing viðkomandi aðgerðar, þ.e.
        Notkun/Fyrir/Eftir.
        Athugið að fastayrðingin verður að hafa
        tvö tilvik, eitt fyrir tóma biðröð og
        annað fyrir biðröð sem ekki er tóm.
        
       Data invariant:
        Write here a loop invariant in Icelandic or
        English, which should correspond to the
        invariant in the Dafny file H10.dfy, (i.e.
        the predicate Valid()). Try to be concise
        and precise. It is necessary that the data
        invariant be true after the construction of
        an object of type E10<T> and give enough
        information so that a programmer can 
        implement the constructor and each of the
        methods isEmpty(), put(x) and get()
        without knowing the implementations of the
        other operations.
        The only information that should be needed
        to implement each of the operations should
        be the data invariant end the description
        of the operation, i.e. Usage/Pre/Post.
        Note that the data invariant needs two
        versions, one for an empty queue and another
        for a queue that is not empty.

        ...
    */
    
    // Notkun: E10<T> q = new E10<T>();
    // Fyrir:  Ekkert (annað en að T er hluttag).
    // Eftir:  q vísar á nýja tóma biðröð hluta af
    //         tagi T.
    // Usage:  E10<T> q = new E10<T>();
    // Pre:    Nothing (except that T is an object type)
    // Post:   q refers to a new empty queue of objects
    //         of type T.
    public E10()
    {
        ...
    }
    
    // Notkun: ...
    // Fyrir:  ...
    // Eftir:  ...
    // Usage:  ...
    // Pre:    ...
    // Post:   ...
    public void put( T x )
    {
        ...
    }
    
    // Notkun: ...
    // Fyrir:  ...
    // Eftir:  ...
    // Usage:  ...
    // Pre:    ...
    // Post:   ...
    public boolean isEmpty()
    {
        ...
    }
    
    // Notkun: ...
    // Fyrir:  ...
    // Eftir:  ...
    // Usage:  ...
    // Pre:    ...
    // Post:   ...
    public T get()
    {
        ...
    }
    
    // Notkun: Af skipanalínunni:
    //           java E10 1 2 3 4 5
    // Eftir:  Búið er að skrifa
    //           1 2 3 4 5
    //         á aðalúttak.
    // Usage:  In a command line:
    //           java E10 1 2 3 4 5
    // Post:   The following has been written
    //           1 2 3 4 5
    //         to stdout.
    public static void main( String[] args )
    {
        E10<String> q = new E10<String>();
        for( int i=0 ; i!=args.length ; i++ ) q.put(args[i]);
        while( !q.isEmpty() ) System.out.print(q.get()+" ");
    }
}