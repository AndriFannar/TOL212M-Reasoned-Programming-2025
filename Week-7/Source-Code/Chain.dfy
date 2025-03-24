// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

// Klasi fyrir eintengda lista breytanlegra hlekkja.
// A class for singly linked lists of mutable links.
class Link<T>
{
    var head: T
    var tail: Link?<T>
    
    // x.ValidChain(chain) er satt þá og því aðeins
    // að x vísi á fremsta hlekk í keðju þeirra
    // hlekkja sem chain inniheldur. Aftasti
    // hlekkurinn í þeirri keðju verður að hafa
    // tail==null.
    // x.Valid(chain) is true if and only if x
    // refers to the first link in the chain of
    // the links that chain contains. The last
    // link must have tail==null.
    ghost predicate ValidChain( chain: seq<Link<T>> )
        reads this, chain
        decreases chain
    {
        if tail == null then
            chain == [this]
        else
            |chain| > 1 &&
            this == chain[0] &&
            tail == chain[1] &&
            tail.ValidChain(chain[1..]) &&
            chain[|chain|-1].tail == null &&
            forall i | 0 <= i < |chain|-1 :: chain[i].tail == chain[i+1]
    }
    
    // Smiðurinn gerir okkur kleift að skeyta nýjum hlekk
    // framan á löglega keðju, sem gefur þá lengri keðju.
    // The constructor enables us to prepend a new link
    // to a valid chain, giving a longer chain.
    constructor( h: T, x: Link?<T>, ghost chain: seq<Link<T>> )
        requires (x == null && chain == []) || (x != null && x.ValidChain(chain))
        ensures ValidChain([this]+chain)
        ensures head == h
        ensures tail == x
    {
        head := h;
        tail := x;
    }    
}

// ValueSeq(x) er runa gildanna sem hlekkirnir  í x innihalda.
// ValueSeq(x) is the sequence of values contained in x.
function ValueSeq<T>( x: seq<Link<T>> ): seq<T>
    reads x
{
    if x == [] then [] else ValueSeq(x[..|x|-1])+[x[|x|-1].head]
}

// Append1 gerir okkur kleift að bæta nýjum hlekk aftan á keðju.
// Append1 enables us to append a new link to a chain.
method Append1<T>( first: Link?<T>, ghost chain: seq<Link<T>>, last: Link?<T>, x: T )
        returns( newfirst: Link<T>, ghost newchain: seq<Link<T>>, newlast: Link<T> )
    modifies if chain == [] then [] else chain[|chain|-1..]
    requires first == null ==>
                chain == [] &&
                last == null
    requires first != null ==>
                first.ValidChain(chain) &&
                last != null &&
                last == chain[|chain|-1] &&
                last.ValidChain([last])
    ensures fresh(newlast)
    ensures newlast.ValidChain([newlast])
    ensures newchain == chain+[newlast]
    ensures newfirst.ValidChain(newchain)
    ensures newlast.head == x
    ensures ValueSeq(newchain) == ValueSeq(chain)+[x]
    ensures ValueSeq(chain) == old(ValueSeq(chain))
{
    newlast := new Link<T>(x,null,[]);
    if last == null
    {
        newfirst := newlast;
        newchain := [newlast];
        return;
    }
    newfirst := first;
    TailSeqLemma(chain);
    last.tail := newlast;
    TailSeqLemma(chain);
    newchain := chain+[newlast];
    ghost var i := |newchain|-1;
    while i != 0
        decreases i
        invariant 0 <= i < |newchain|
        invariant newchain[i].ValidChain(newchain[i..])
    {
        i := i-1;
    }
}

// Prepend1 gerir okkur kleift að bæta nýjum hlekk framan á keðju.
// Prepend1 enables us to prepend a new link to a chain.
method Prepend1<T>( first: Link?<T>, ghost chain: seq<Link<T>>, last: Link?<T>, x: T )
        returns( newfirst: Link<T>, ghost newchain: seq<Link<T>>, newlast: Link<T> )
    requires first == null ==>
                chain == [] &&
                last == null
    requires first != null ==>
                first.ValidChain(chain) &&
                last != null &&
                last == chain[|chain|-1] &&
                last.ValidChain([last])
    ensures fresh(newfirst)
    ensures newlast.ValidChain([newlast])
    ensures newchain == [newfirst]+chain
    ensures newfirst.ValidChain(newchain)
    ensures newfirst.head == x
    ensures ValueSeq(chain) == old(ValueSeq(chain))
    ensures ValueSeq(newchain) == [x]+ValueSeq(chain)
{
    newfirst := new Link(x,first,chain);
    if first == null
    {
        newlast := newfirst;
    }
    else
    {
        newlast := last;
    }
    newchain := [newfirst]+chain;
    ConcatValueSeq([newfirst],chain);
}

// Augljós sannindi um samskeytingar hlekkjaruna.
// Obvious truths about concatenations of sequences of links.
lemma ConcatValueSeq<T>( x: seq<Link<T>>, y: seq<Link<T>> )
    decreases y
    ensures ValueSeq(x+y) == ValueSeq(x)+ValueSeq(y)
{
    if y == []
    {
        assert x+y == x;
        return;
    }
    ConcatValueSeq(x,y[..|y|-1]);
    assert y == y[..|y|-1]+[y[|y|-1]];
    assert x+y == x+y[..|y|-1]+[y[|y|-1]];
}

// Augljós sannindi um hlekkjarunur og samsvarandi gildarunur.
// Obviuc truths about link sequences and coresponding value sequences.
lemma TailSeqLemma<T>( x: seq<Link<T>> )
    ensures |ValueSeq(x)| == |x|
    ensures forall i | 0 <= i < |x| :: ValueSeq(x)[i] == x[i].head
{
    if x == [] { return; }
    TailSeqLemma(x[..|x|-1]);
    assert x[|x|-1].head == ValueSeq(x)[|x|-1];
}

// Ýmis gagnleg sannindi um hlekkjarunur og samsvarandi gildarunur.
// Various useful truths about link sequences and corresponding value sequences.
lemma ValueSeqLemma<T>( x: seq<Link<T>>, y: seq<T> )
    requires |x| != 0
    requires y == ValueSeq(x)
    ensures |x| == |y|
    ensures x[0].head == y[0]
    ensures y == ValueSeq(x[..1])+ValueSeq(x[1..])
    ensures x == x[..1]+x[1..]
    ensures y == y[..1]+y[1..]
    ensures ValueSeq(x[1..]) == y[1..]
    ensures |x| == |y|
{
    TailSeqLemma(x);
    if |x| == 1 { return; }
    TailSeqLemma(x[..1]);
    TailSeqLemma(x[1..]);
    ValueSeqLemma(x[..|x|-1],y[..|x|-1]);
    assert x == x[..1]+x[1..];
    assert x == x[..|x|-1]+x[|x|-1..];
    assert |y| == |x|;
    assert y == y[..1]+y[1..];
    assert y == y[..|x|-1]+y[|x|-1..];
}
