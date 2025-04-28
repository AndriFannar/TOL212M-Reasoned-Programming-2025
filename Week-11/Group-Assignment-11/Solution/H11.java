// Tilvik af H11<T> eru forgangsbiðraðir hluta af tagi T.
// Tilvik af H11<T> er aðeins hægt að búa til fyrir klasa T
// sem eru Comparable, þ.e. tilvik af T eru samanburðarhæf hvort
// við annað, með þeim samningi sem því fylgir.

// Skilgreiningar (þetta má skilgreina formlega í Dafny):
//
//   Í fylki a sem inniheldur sæti i segjum við að sæti 2*i+1 og
//   2*i+2 séu börn sætis i, ef þau eru til staðar í fylkinu.
//   Á svipaðan hátt segjum við að fyrir sæti i > 0 sé sæti
//   floor((i-1)/2) foreldri sætis i.
//
//   Við skilgreinum að sæti 2*i+1 og 2*i+2 séu afkomendur sætis
//   i og við skilgreinum einnig að ef sæti k er afkomandi j og
//   j er afkomandi i þá er k afkomandi i (gegnvirkni, transitivity).
//
//   Fyrir svæði a[i..j) í fylki samanburðarhæfra gilda segjum við
//   að svæðið uppfylli hrúguskilyrði þá og því aðeins að fyrir
//   sérhver tvö sæti n og m innan svæðisins, þar sem m er afkomandi
//   n gildi að bæði a[m] og a[n] eru lögleg gildi (ekki null, til
//   dæmis) og a[m] <= a[n], þ.e. a[m].compareTo(a[n]) <= 0.
//
//   Við segjum einnig að svæði a[0..j) sé hrúga ef svæðið
//   uppfyllir hrúguskilyrði.
//
//   Setning: Ef a[i..j) er svæði í fylki og j < 2*i+1 þá uppfyllir
//   svæðið hrúguskilyrði því ekkert sæti innan svæðisins er
//   afkomandi annars sætis innan svæðisins. Jafngilt skilyrði er
//   þegar i > floor((j-1)/2) eða þegar i >= floor((j-1)/2)+1.
//
//   Setning (sannanleg í Dafny): Ef a[0..j) er hrúga þá er a[0]
//   stærsta gildið í svæðinu (ef j != 0, að sjálfsögðu).
//
//   Takið eftir að hrúga a[0..j) er tvíundartré með j hnúta í
//   eins miklu jafnvægi og hægt er að öðlast með j hnúta tré.

// Instances of H11<T> are priority queues of objects of type T.
// Instances of H11<T> can only be constructed for classes T
// that are Comparable, i.e. instances of T are comparable to
// each other, with the contract that this entails.

// Definitions (this can be formally defined in Dafny):
//
//   In an array a that contains a position i we say that positions
//   2*i+1 and 2*i+2 are the children of position i, if they exist
//   in the array.
//   Similarly we say that for i > 0 the position floor((i-1)/2) is
//   the parent of position i.
//
//   We define positions 2*i+1 and 2*i+2 to be descendants of position
//   i and we also define that if position k is the descendant of j and
//   position j is the descendant of i then k is also the a descendant
//   of i (transitivity).
//
//   For a section a[i..j) in an array of comparable objects we say
//   that the section fulfills the heap condition if and only if
//   for every pair of positions n and m inside the section, where
//   m is a descendant of n and neither a[m] nor a[n] is null we
//   have a[m] <= a[n], i.e. a[m].compareTo(a[n]) <= 0.
//
//   We also say that a section a[0..j) is a heap if the section
//   fulfills the heap condition.
//
//   Theorem: If a[i..j) is a section in an array and j < 2*i+1 then
//   the section fulfills the heap condition because no position
//   is the descendant of another position within the section.
//   An equivalent requirement is when i > floor((j-1)/2) or when
//   i >= floor((j-1)/2)+1.
//
//   Theorem (provable in Dafny): If a[0..j) is a heap then a[0]
//   is the biggest value in the section (if j != 0, of course).
//
//   Note that a heap a[0..j) is a binary tree with j nodes and
//   is as balanced as a binary tree with j nodes can be.

public class H11< T extends Comparable<? super T>>
{
    private T[] a;
    private int n;
    // draugabreyta/ghost variable multiset<T> m;

    // Fastayrðing gagna:
    //    Forgangsbiðröð sem inniheldur gildin t1,t2,...,tN
    //    hefur
    //      1) m==multiset{t1,t2,...,tN}
    //      2) n==N
    //      3) a.length >= n
    //      4) mulltiset(a[0..n)) == m
    //      5) a[0..n) er hrúga
    //
    //    Fastayrðingin er (í Java, ekki í Dafny) sjálfgefinn
    //    hluti af eftirskilyrði allra opinberra aðgerða, þar með
    //    talið allra smiða. Einnig er fastayrðingin sjálfgefinn
    //    hluti forskilyrðis allra opinberra boða annarra en
    //    smiða.

    // Data invariant:
    //    A priority queue that contains the values t1,t2,...,tN
    //    has:
    //      1) m==multiset{t1,t2,...,tN}
    //      2) n==N
    //      3) a.length >= n
    //      4) multiset(a[0..n)) == m
    //      5) a[0..n) is a heap
    //    Remember that the data invariant (in Java, not in Dafny) is
    //    an implicit part of the postcondition for all public
    //    operations and is also an imolicit part of the precondition
    //    for each public operation except constructors.

    // Notkun: H11<T> pq = new HeadPriQueue<T>();
    // Fyrir:  Ekkert (annað en að T verður að vera löglegt).
    // Eftir:  pq er ný tóm forgangsbiðröð gilda af tagi T
    //         með pláss fyrir ótakmarkaðan fjölda gilda.
    // Usage:  H11<T> pq = new H11<T>();
    // Pre:    Nothing (other than that T must be legal).
    // Post:   pq is a new empty priority queue for values of type T
    //         with space for an unlimited number of values.
    public H11()
    {
        a = (T[]) new Comparable<?>[100];
        n = 0;
    }

    // Notkun: rollDown(a,i,j);
    // Fyrir:  a[i..j) og a[i+1..j) eru svæði í a.
    //         a[i+1..j) uppfyllir hrúguskilyrði.
    // Eftir:  a[i..j) inniheldur sömu gildi og áður,
    //         en þeim hefur verið umraðað þannig að
    //         a[i..j) uppfyllir nú hrúguskilyrði.
    // Usage:  rollDown(a,i,j);
    // Pre:    a[i..j) and a[i+1..j) are sections of a.
    //         a[i+1..j) fulfills the heap condition.
    // Post:   a[i..j) contains the same values as before,
    //         but they have been permuted in such a way
    //         that a[i..j) fulfills the heap condition.
    public static<E extends Comparable<? super E>> void rollDown( E[] a, int i, int j )
    {
        // Hér vantar forritstexta.
        // Hér ætti að vera lykkja með fastayrðingu sem getur verið
        // eitthvað a þessa leið:
        //   ? <= k < ?
        //   Allir samanburðir milli sæta p < q í svæðinu a[i..j)
        //   eru í samræmi við hrúguskilyrði nema e.t.v. í þeim
        //   tilvikum þegar ???.
        // Here we need program text vantar forritstexta.
        // Here we should have a loop with a loop invariant which
        // could say something like this:
        //   ? <= k < ?
        //   All comparisons between positions p < q in a[i..j) are
        //   in conformance to the heap condition except possibly
        //   when ???.

        int k = i;
        for(;;)
        {
            // i <= k < j.
            // Allir samanburðir milli sæta p < q í svæðinu a[i..j) eru
            // í samræmi við hrúguskilyrði nema e.t.v. í þeim tilvikum þegar
            // p == k.
            //
            // i <= k < j.
            // All comparisons between positions p < q in a[i..j) are
            // in conformance to the heap condition except possibly
            // when p == k.
            int c = 2*k+1;
            if( c >= j ) return;
            if( c+1 < j && a[c].compareTo(a[c+1]) < 0 ) c++;
            if( a[k].compareTo(a[c]) >= 0 ) return;
            E tmp = a[k];
            a[k] = a[c];
            a[c] = tmp;
            k = c;
        }
    }

    // Notkun: rollUp(a,i,j);
    // Fyrir:  a[i..j) og a[i..j+1) eru svæði í a.
    //         a[i..j) uppfyllir hrúguskilyrði.
    // Eftir:  a[i..j+1) inniheldur sömu gildi og áður,
    //         en þeim hefur verið umraðað þannig að
    //         a[i..j+1) uppfyllir nú hrúguskilyrði.
    // Usage:  rollUp(a,i,j);
    // Pre:    a[i..j) and a[i..j+1) are sections of a.
    //         a[i..j) fulfills the heap condition.
    // Post:   a[i..j+1) contains the same values as before,
    //         but they have been permuted in such a way
    //         that a[i..j+1) fulfills the heap condition.
    public static<E extends Comparable<? super E>> void rollUp( E[] a, int i, int j )
    {
        // Hér vantar forritstexta.
        // Hér ætti að vera lykkja með fastayrðingu sem getur verið
        // eitthvað a þessa leið:
        //   ? <= k <= ?
        //   Allir samanburðir milli sæta p < q í svæðinu a[i..j+1)
        //   eru í samræmi við hrúguskilyrði nema e.t.v. í þeim
        //   tilvikum þegar ???.
        // Here we need program text vantar forritstexta.
        // Here we should have a loop with a loop invariant which
        // could say something like this:
        //   ? <= k < ?
        //   All comparisons between positions p < q in a[i..j+1) are
        //   in conformance to the heap condition except possibly
        //   when ???.
        
        int k = j;
        while( (k-1)/2 >= i )
        {
            // i <= k <= j.
            // Allir samanburðir milli sæta p < q í svæðinu a[i..j+1) eru
            // í samræmi við hrúguskilyrði nema e.t.v. í þeim tilvikum þegar
            // q == k.
            //
            // i <= k < j+1.
            // All comparisons between positions p < q in a[i..j+1) are
            // in conformance to the heap condition except possibly
            // when q == k.
            int p = (k-1)/2;
            if( a[p].compareTo(a[k]) >= 0 ) return;
            E tmp = a[p];
            a[p] = a[k];
            a[k] = tmp;
            k = p;
        }
    }
    
    // Notkun: sort(a);
    // Fyrir:  a er fylki gilda af tagi E (og E er löglegt).
    // Eftir:  a hefur verið raðað í vaxandi röð.
    // Usage:  sort(a);
    // Pre:    a is an array of E objects (and E is legal).
    // Post:   a has been sorted in ascending order.
    public static<E extends Comparable<? super E>> void sort( E[] a )
    {
        // Hér vantar forritstexta.
        // Þetta skal útfæra á hraðvirkan hátt, þ.e. O(n log(n)),
        // annaðhvort með því að nota einungis rollDown í tveimur
        // lykkjum, eða með því að nota rollUp í einni lykkju og
        // rollDown í annarri lykkju.
        // Here we need program text.
        // This should have time complexity O(n log(n)), either
        // by using two loops with rollDown or one loop with
        // rollUp and one with rollDown.
        
        int k = (a.length-1)/2+1;
        // Ef a.length er oddatala þá er 2*k+1 == a.length-1+2 == a.length+1.
        // Ef a.length er slétt tala þá er 2*k+1 == a.length-2+2 == a.length.
        // Í báðum tilvikum er 2*k+1 utan fylkisins.
        // If a.length is odd then 2*k+1 == a.length-1+2 == a.length+1.
        // If a.length is even then 2*k+1 == a.llength-2+2 == a.length.
        // In both cases 2*k+1 is outside the bounds of the array.
        while( k != 0 )
        {
            // a inniheldur sömu gildi og áður, en e.t.v. umröðuð.
            // a[k..] uppfyllir hrúguskilyrði.
            // 0 <= k <= a.length.
            // a contains the same values as originally, but perhaps permuted.
            // a[k..] fulfills the heap condition.
            // 0 <= k <= a.length.
            rollDown(a,--k,a.length);
        }
        k = a.length;
        while( k > 1 )
        {
            // a inniheldur sömu gildi og áður, en e.t.v. umröðuð.
            // a[0..k) er hrúga.
            // a[k..] inniheldur stærstu gildi a í vaxandi röð.
            // a contains the same values as originaLLY, but perhaps permuted.
            // a[0..k) is a heap.
            // a[k..] contains the largest values in ascending order.
            E tmp = a[0];
            a[0] = a[--k];
            a[k] = tmp;
            rollDown(a,0,k);
        }
    }
    
    // Notkun: int n = pq.count();
    // Fyrir:  pq er forgangsbiðröð.
    // Eftir:  n er fjöldi gilda í pq.
    // Usage:  int n = pq.count();
    // Pre:    pq is a priority queue.
    // Post:   n is the number of values in pq.
    public int count()
    {
        // Hér vantar forritstexta.
        // Here we need program text.
        return n;
    }
    
    // Skrifið lýsingu hér
    // Notkun: T x = pq.deleteMax();
    // Fyrir:  pq er forgangsbiðröð, ekki tóm.
    // Eftir:  x er stærsta gildið sem var í pq, en það
    //         hefur verið fjarlægt og pq inniheldur því
    //         einum færri gildi en áður.
    // Write a description here
    // Usage:  T x = pq.deleteMax();
    // Pre:    pq is a priority queue, not empty.
    // Post:   x is the largest value that was in pq, but
    //         it has been removed from pq and pq now
    //         contains one less value.
    public T deleteMax()
    {
        // Hér vantar forritstexta.
        // Notið rollDown til að útfæra aðgerðina.
        // Munið að uppfæra einnig draugabreytuna m.
        // Here we need program text.
        // Use rollDown to implement the method.
        // Remember to also update the ghost variable m.
        T tmp = a[0];
        a[0] = a[--n];
        rollDown(a,0,n);
        // m = m-multiset{tmp};
        return tmp;
    }
    
    // Skrifið lýsingu hér
    // Notkun: pq.put(x);
    // Fyrir:  pq er forgangsbiðröð og x er af tagi T.
    // Eftir:  x hefur verið bætt í pq.
    // Write a description here
    // Usage:  pq.put(x);
    // Pre:    pq is a priority queue and x is of type T.
    // Eftir:  x has been added to pq.
    public void put( T x )
    {
        // Hér vantar forritstexta.
        // Notið rollUp til að útfæra aðgerðina.
        // Munið að uppfæra einnig draugabreytuna m.
        // Athugið að undir einhverjum kringumstæðum þurfið þið að
        // stækka fylkið a. Eðlilegt er þá að tvöfalda stærðina.
        // Notið viðeigandi fastayrðingu í lykkjunni þegar þið
        // afritið frá gamla fylkinu yfir í nýja.
        // Here we need program text.
        // Use rollUp to implement the method.
        // Remember to also update the ghost variable m.
        // Note that under some circumstances you need to increase
        // the size of the array a. It is then natural to double the
        // size. Use an appropriate loop invariant when you copy
        // from the old array t the new one.
        if( n == a.length )
        {
            T[] newa = (T[])new Comparable<?>[2*n];
            for( int i=0 ; i!=n ; i++ )
            {
                // 0 <= i <= n.
                // newa.length > a.length.
                // newa[0..i) == a[0..i).
                // a er óbreytt / a is unchanged.
                newa[i] = a[i];
            }
            a = newa;
        }
        a[n] = x;
        rollUp(a,0,n++);
        // m = m+multiset{x};
    }
    
    // Prófið að keyra 
    //   java H11 1 2 3 4 10 20 30 40
    // Það ætti að skrifa
    //   1 10 2 20 3 30 4 40
    //   40 4 30 3 20 2 10 1    
    // Try running 
    //   java H11 1 2 3 4 10 20 30 40
    // this should write
    //   1 10 2 20 3 30 4 40
    //   40 4 30 3 20 2 10 1    
    public static void main( String[] args )
    {
        sort(args);
        for( int i=0 ; i!=args.length ; i++ ) System.out.print(args[i]+" ");
        System.out.println();
        H11<String> pq = new H11<String>();
        for( int i=0 ; i!=args.length ; i++ ) pq.put(args[i]);
        while( pq.count() != 0 ) System.out.print(pq.deleteMax()+" ");
    }
}