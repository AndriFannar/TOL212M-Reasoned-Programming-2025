// Hér er skilgreiningin á breytanlegum hlekkjum
// sem notaðir eru í hringtengdum keðjum.
// Here is the definition of mutable links
// that are used in circular queues.
class Link<T>
{
    var head: T
    var tail: Link<T>
    
    // x.ValidCycle(cycle) er satt þá og því aðeins
    // að x vísi á aftasta hlekk í hringkeðju þeirra
    // hlekkja sem chain inniheldur. Aftasti
    // hlekkurinn í þeirri keðju verður að hafa
    // tail sem vísar á fremsta.
    // x.ValidCycle(cycle) is true if and only if
    // x refers to the last link in a circular chain
    // of the links contained in chain. The last link
    // in the chain must have a tail that refers to
    // the first link.
    ghost predicate ValidCycle( cycle: seq<Link<T>> )
        reads this, cycle
    {
        |cycle| > 0 &&
        this == cycle[|cycle|-1] &&
        tail == cycle[0] &&
        tail.ValidSequence(cycle) &&
        forall p,q | 0 <= p < q < |cycle| ::
            cycle[p] != cycle[q]
    }
    
    // x.ValidSequence(s) er satt þá og því aðeins að
    // hlekkurinn x sé sá fremsti í keðju hlekkjanna
    // í rununni s og að keðjan sé tengd í þeirri röð.
    // x.ValidSequence(s) is true if and only if the
    // link x is the first link in the chain of links
    // in the sequence s and the chain is linked
    // together in that order.
    ghost predicate ValidSequence( sequence: seq<Link<T>> )
        reads this, sequence
    {
        |sequence| > 0 &&
        this == sequence[0] &&
        forall i | 0 <= i < |sequence|-1 ::
            sequence[i].tail == sequence[i+1]
    }
    
    // Smiðurinn gerir okkur kleift að skeyta nýjum hlekk
    // inn í hringkeðju, sem gefur þá lengri hringkeðju
    // með nýjum aftasta hlekk.
    // Þessi smiður virkar á þægilegan hátt miðað við
    // fastayrðingu gagna í biðraðaklasa sem útfærður
	// er með hringkeðju hlekkja.
    // The constructor makes it possible to insert a new
    // link into a circular chain, which then gives us
    // a longer circular chain with a new last link.
    // This constructor works in a convenient fashion
    // considering the data invariant for a queue class
    // implemented as a circular chain.
    
    // Notkun: Link<T> y := new Link(h,x,cycle,values);
    // Fyrir:  x er Link?<T> og ef x er null þá eru
    //         runurnar cycle og values báðar tómar.
    //         Annars vísar x á aftasta hlekk í hringkeðju
    //         hlekkjanna í cycle, sem innihalda gildin
    //         í values.
    // Eftir:  y vísar á nýjan hlekk í hringkeðju sem
    //         inniheldur alla hlekkina úr x, ásamt þessum
    //         nýja hlekk.  Ef x er null þá inniheldur
    //         þessi hringkeðja aðeins þann eina hlekk,
    //         annars var nýja hlekknum skeytt inn fyrir
    //         aftan hlekkinn sem x bendir á.
    // Usage:  Link<T> y := new Link(h,x,cycle,values);
    // Pre:    x is a Link?<T> and if x is null then
    //         the sequences cycle and values are both empty.
    //         Otherwise x refers to the last link in a
    //         circular chain of the links in cycle, that
    //         contain the values in the argument values.
    // Post:   y refers to a new link in a circular chain that
    //         contains all the links from x, as well as this
    //         new link. If x is null then this circular chain
    //         onlly contains this new link, but otherwise the
    //         new link is appended to the last link and becomes
    //         the new last link.
    constructor( h: T, x: Link?<T>, ghost cycle: seq<Link<T>>, ghost values: seq<T> )
        modifies if cycle != [] then {cycle[|cycle|-1]} else {}
        requires (x == null && cycle == []) || (x != null && x.ValidCycle(cycle))
        requires values == ValueSeq(cycle)
        requires forall i | 0 <= i < |cycle| :: cycle[i].head == values[i]
        ensures head == h
        ensures tail == if x == null then this else cycle[0]
        ensures fresh(this)
        ensures forall i | 0 <= i < |cycle| :: cycle[i].head == values[i]
        ensures forall i | 0 <= i < |cycle| :: cycle[i].head == old(cycle[i].head)
        ensures forall z | z in cycle :: z.head == old(z.head)
        ensures ValueSeq(cycle) == values
        ensures ValidCycle(cycle+[this])
        ensures ValueSeq(cycle+[this]) == values+[h]
    {
        head := h;
        tail := this;
        new;
        if x != null
        {
            tail := x.tail;
            x.tail := this;
            HeadsEqual(cycle,values);
            AppendLink(cycle,this);
        }
    }    
}

// Fallið RemoveFirst gerir okkur kleift að fjarlægja
// viðeigandi hlekk úr hringkeðju hlekkja. Virkni þessa
// falls er þægileg miðað við fastayrðingu gagna í
// biðröð sem notar hringkeðjur.
// The method RemoveFirst enables us to remove the
// appropriate link from a circular chain of links.
// The functionality of the method is convenient
// considering the data invariant in a queue implemented
// using a circular chain.
method RemoveFirst<T>   ( last: Link<T>
                        , ghost cycle: seq<Link<T>>
                        , ghost vals: seq<T>
                        )
        returns ( newlast: Link?<T>
                , ghost newcycle: seq<Link<T>>
                , ghost newvals: seq<T>
                )
    modifies last
    requires last.ValidCycle(cycle)
    requires ValueSeq(cycle) == vals
    requires |vals| == |cycle|
    requires |vals| > 0
    ensures last.head == old(last.head)
    ensures |vals| == 1 ==>
                    newlast == null &&
                    newcycle == [] &&
                    newvals == []
    ensures |vals| > 1 ==>
                    newlast == last &&
                    newcycle == cycle[1..] &&
                    newlast.ValidCycle(cycle[1..]) &&
                    newvals == vals[1..] &&
                    ValueSeq(newcycle) == newvals
{
    if last.tail == last
    {
        newlast := null;
        newcycle := [];
        newvals := [];
        return;
    }
    ValueSeqHeads(cycle,vals);
    newlast := last;
    newcycle := cycle[1..];
    newvals := vals[1..];
    newlast.tail := newlast.tail.tail;
    HeadsEqual(cycle[1..],vals[1..]);
}

function ValueSeq<T>( x: seq<Link<T>> ): seq<T>
    reads x
    ensures |x| == |ValueSeq(x)|
{
    if x == [] then
        []
    else
        [x[0].head]+ValueSeq(x[1..])
}

lemma ValueSeqHeads<T>( x: seq<Link<T>>, v: seq<T> )
    requires v == ValueSeq(x)
    ensures forall i | 0 <= i < |x| :: x[i].head == v[i]
{
    if |x| == 0 { return; }
    ValueSeqHeads(x[1..],v[1..]);
}

lemma AppendLink<T>( x: seq<Link<T>>, z: Link<T> )
    ensures ValueSeq(x+[z]) == ValueSeq(x)+[z.head]
{
    if x == [] { return; }
    AppendLink(x[1..],z);
    calc ==
    {
        x+[z];
        (x[..1]+x[1..])+[z];
        x[..1]+(x[1..]+[z]);
    }
}

lemma HeadsEqual<T>( x: seq<Link<T>>, v: seq<T> )
    requires |x| == |v|
    requires forall i | 0 <= i < |x| :: x[i].head == v[i]
    ensures ValueSeq(x) == v
{
    if |x| == 0 { return; }
    HeadsEqual(x[1..],v[1..]);
}