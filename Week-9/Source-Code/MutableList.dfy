// Author: Snorri Agnarsson, snorri@hi.is

// An experiment with mutable lists.

// Dafny is barely able to verify this.
// The command line compiler usually verifies on my computer,
// but not always Visual Studio Code.

class Link
{
    var head: int
    var tail: Link?
}

class FiniteList
{
    ghost var linkseq: seq<Link>
    ghost var intseq: seq<int>
    var list: Link?

    ghost predicate Valid()
        reads this, this.list, linkseq
    {
        IsSameChain(list,linkseq) &&
        |intseq| == |linkseq| &&
        (forall p,q | 0 <= p < q < |linkseq| :: linkseq[p] != linkseq[q]) &&
        ((list == null) <==> ((intseq == []) && (linkseq == []))) &&
        (forall i,j | 0 <= i < j < |intseq| :: linkseq[i] != linkseq[j]) &&
        (forall i | 0 <= i < |intseq| :: intseq[i] == linkseq[i].head) &&
        (forall i | 0 < i < |intseq| :: linkseq[i-1].tail == linkseq[i]) &&
        (forall i | 0 <= i < |intseq|-1 :: linkseq[i].tail == linkseq[i+1]) &&
        (forall i | 0 <= i < |intseq| :: linkseq[i].tail == null ==> i == |intseq|-1) &&
        (linkseq != [] ==> linkseq[|linkseq|-1].tail == null) &&
        (list != null ==> linkseq != [] && linkseq[0] == list)
    }

    constructor( x: seq<int> )
        ensures Valid()
        ensures intseq == x
        ensures fresh(linkseq)
    {
        list := null;
        linkseq := [];
        intseq := [];
        new;
        if x == [] { return; }
        var i := |x|;
        list := null;
        linkseq := [];
        intseq := [];
        while i != 0
            decreases i
            invariant 0 <= i <= |x|
            invariant |linkseq| == |x|-i
            invariant fresh(linkseq)
            invariant intseq== x[i..]
            invariant Valid()
        {
            var tmp := new Link;
            i := i-1;
            tmp.head := x[i];
            tmp.tail := list;
            list := tmp;
            linkseq := [tmp]+linkseq;
            intseq := [x[i]]+intseq;
        }
    }

    method IntSeq() returns ( s: seq<int> )
        requires Valid()
        ensures s == intseq
    {
        s := [];
        var nextLink := list;
        while nextLink != null
            decreases |intseq|-|s|
            invariant 0 <= |s| <= |intseq|
            invariant s == intseq[..|s|]
            invariant Valid()
            invariant linkseq == old(linkseq)
            invariant intseq == old(intseq)
            invariant forall r | 0 <= r < |linkseq| :: linkseq[r].head == old(linkseq[r].head)
            invariant forall r | 0 <= r < |linkseq| :: linkseq[r].tail == old(linkseq[r].tail)
            invariant nextLink != null ==> |s| < |linkseq| && nextLink == linkseq[|s|]
            invariant
                if |s| < |intseq| then
                    nextLink == linkseq[|s|]
                else
                    |s| == |linkseq| &&
                    nextLink == null
        {
            s := s+[nextLink.head];
            nextLink := nextLink.tail;
        }
    }

    method Length() returns( n: int )
        requires Valid()
        ensures n == |linkseq|
    {
        if list == null { return 0; }
        var next: Link := list;
        n := 0;
        while next.tail != null
            invariant Valid()
            decreases |linkseq| - n
            invariant 0 <= n < |linkseq|
            invariant next == linkseq[n]
        {
            next := next.tail;
            n := n+1;
        }
        return n+1;
    }

    function Head(): int
        reads this, list, linkseq
        requires Valid()
        requires |linkseq| != 0
        ensures Head() == list.head
    {
        list.head
    }

    method Tail() returns ( r: FiniteList )
        requires Valid()
        requires |linkseq| != 0
        ensures r.Valid()
        ensures r.linkseq == old(linkseq)[1..]
        ensures r.intseq == old(intseq)[1..]
    {
        r := new FiniteList([]);
        r.list := list.tail;
        r.linkseq := linkseq[1..];
        r.intseq := intseq[1..];
    }

    method DeepClone() returns ( r: FiniteList )
        requires Valid()
        ensures r.Valid()
        ensures r != this
        ensures fresh(r)
        ensures r.intseq == intseq
        ensures fresh(r.linkseq)
        ensures forall z | z in r.linkseq :: z !in linkseq
        ensures linkseq == old(linkseq)
    {
        var s := IntSeq();
        r := new FiniteList(s);
    }

    method ConsInt( x: int )
        requires Valid()
        modifies this
        ensures Valid()
        ensures linkseq != []
        ensures fresh(linkseq[0])
        ensures intseq[0] == x
        ensures linkseq[1..] == old(linkseq)
        ensures intseq[1..] == old(intseq)
    {
        var newLink := new Link;
        newLink.head := x;
        newLink.tail := list;
        list := newLink;
        linkseq := [newLink]+linkseq;
        intseq := [x]+intseq;
    }

    method ConsLink( x: Link, other: FiniteList )
        requires Valid()
        requires other.Valid()
        requires this != other
        modifies this, x
        //reads other.linkseq
        requires x !in linkseq
        requires x !in other.linkseq
        requires forall u, v | u in linkseq && v in other.linkseq :: u != v
        ensures Valid()
        ensures other.Valid()
        ensures linkseq == [x]+old(linkseq)
        ensures x.head == old(x.head)
        ensures intseq == [x.head]+old(intseq)
        ensures other.linkseq == old(other.linkseq)
        ensures other.intseq == old(other.intseq)
        ensures forall u, v | u in linkseq && v in other.linkseq :: u != v
    {
        x.tail := list;
        list := x;
        linkseq := [x]+linkseq;
        intseq := [x.head]+intseq;
    }

    method RemoveHead() returns ( r: Link )
        requires Valid()
        modifies this
        requires |linkseq| > 0
        ensures Valid()
        ensures intseq == old(intseq[1..])
        ensures linkseq == old(linkseq[1..])
        ensures r == old(linkseq)[0]
        ensures r !in linkseq
        ensures r in old(linkseq)
        ensures r.head == old(intseq)[0]
    {
        r := list;
        list := list.tail;
        assert forall p | 1 <= p < |linkseq| :: r != linkseq[p];
        linkseq := linkseq[1..];
        intseq := intseq[1..];
    }

    method ConstructiveReverse() returns ( r: FiniteList )
        requires Valid()
        ensures r.Valid()
        ensures fresh(r)
        ensures fresh(r.linkseq)
        ensures IsReverse(intseq,r.intseq)
    {
        r := new FiniteList([]);
        var rest := list;
        ghost var i := 0;
        while rest != null
            invariant 0 <= i <= |linkseq|
            decreases |linkseq|-i
            invariant r.Valid()
            invariant IsReverse(r.intseq,intseq[..i])
            invariant fresh(r)
            invariant fresh(r.linkseq)
            invariant rest == null ==> i == |linkseq|
            invariant rest != null ==> i < |linkseq| && rest == linkseq[i]
        {
            r.ConsInt(rest.head);
            assert i < |linkseq|-1 ==> rest.tail == linkseq[i+1];
            assert i == |linkseq|-1 ==> rest.tail == null;
            rest := rest.tail;
            i := i+1;
        }
    }

    // Dafny has a hard time verifying the following method.
    // On my Windows computer Visual Studio Code eventually verifies,
    // but the command-line Dafny compiler fails.
    // On the other hand the newest command-line Dafny compiler
    // on Ubuntu succeeds in verifying and compiling into
    // a library file MutableList.doo, using the command
    // dafny build MutableList.dfy -t:lib --verification-time-limit:1000 --output:MutableList.doo

    method DestructiveReverse()
        requires Valid()
        modifies this, linkseq
        ensures Valid()
        ensures IsReverse(intseq,old(intseq))
        ensures IsReverse(linkseq,old(linkseq))
    {
        var r := new FiniteList([]);
        ghost var i := 0;
        while list != null
            invariant 0 <= i <= |old(linkseq)|
            decreases |old(linkseq)|-i
            invariant r != this
            invariant r.Valid()
            invariant Valid()
            invariant i == |r.intseq| == |r.linkseq|
            invariant IsReverse(r.intseq,old(intseq)[..i])
            invariant IsReverse(r.linkseq,old(linkseq)[..i])
            invariant linkseq == old(linkseq)[i..]
            invariant intseq == old(intseq)[i..]
            invariant list == null ==> i == |old(linkseq)|
            invariant list != null ==> i < |old(linkseq)|
            invariant list != null ==> list == old(linkseq)[i]
            invariant forall z,w | z in linkseq && w in r.linkseq :: z != w
            invariant forall i, j | 0 <= i < |linkseq| && 0 <= j < |r.linkseq| :: linkseq[i] != r.linkseq[j]
            invariant i < |old(linkseq)| ==> list == old(linkseq)[i]
            invariant i == |old(linkseq)| ==> list == null
            invariant list != null ==> list.head == old(intseq)[i]
        {
            ghost var oldthis := this;
            assert oldthis.Valid();
            assert oldthis.linkseq == linkseq;
            assert oldthis.intseq == intseq;
            ghost var oldlinkseq := linkseq;
            ghost var oldintseq := intseq;
            ghost var oldr := r;
            assert oldr.Valid();
            assert oldr.linkseq == r.linkseq;
            assert oldr.intseq == r.intseq;
            ghost var oldrlinkseq := r.linkseq;
            ghost var oldrintseq := r.intseq;

            // Remove link from old chain
            var linkToRemove := list;
            list := list.tail;
            linkseq := linkseq[1..];
            intseq := intseq[1..];

            // Prove that the old chain is one link shorter and still valid
            // and that the removed link is in neither chain
            assert linkToRemove !in linkseq;
            assert linkToRemove !in r.linkseq;
            assert linkseq == oldlinkseq[1..];
            assert // Same as Valid()
                IsSameChain(list,linkseq) &&
                |intseq| == |linkseq| &&
                (forall p,q | 0 <= p < q < |linkseq| :: linkseq[p] != linkseq[q]) &&
                ((list == null) <==> ((intseq == []) && (linkseq == []))) &&
                (forall i,j | 0 <= i < j < |intseq| :: linkseq[i] != linkseq[j]) &&
                (forall i | 0 <= i < |intseq| :: intseq[i] == linkseq[i].head) &&
                (forall i | 0 < i < |intseq| :: linkseq[i-1].tail == linkseq[i]) &&
                (forall i | 0 <= i < |intseq|-1 :: linkseq[i].tail == linkseq[i+1]) &&
                (forall i | 0 <= i < |intseq| :: linkseq[i].tail == null ==> i == |intseq|-1) &&
                (linkseq != [] ==> linkseq[|linkseq|-1].tail == null) &&
                (list != null ==> linkseq != [] && linkseq[0] == list);

            // Add the removed link as a new link to reversed chain
            linkToRemove.tail := r.list;
            r.list := linkToRemove;
            r.linkseq := [linkToRemove]+r.linkseq;
            r.intseq := [linkToRemove.head]+r.intseq;

            // Prove that the augmented reversed chain is still valid
            assert r.Valid();

            i := i+1;
        }
        assert i == |old(linkseq)|;
        assert old(linkseq)[..i] == old(linkseq);
        assert old(intseq)[..i] == old(intseq);

        // Replace the list with the new reversed list
        list := r.list;
        intseq := r.intseq;
        linkseq := r.linkseq;
    }

}

ghost predicate IsReverse<T>( a: seq<T>, b: seq<T> )
{
    |a| == |b| &&
    forall i | 0 <= i < |a| :: a[i] == b[|b|-i-1]
}

predicate IsSameChain( x: Link?, g: seq<Link> )
    decreases |g|
    reads x,g
{
    if x == null then
        g == []
    else if g == [] then
        false
    else
        |g| >= 1 &&
        x == g[0] &&
        ((x.tail == null) || (x.tail in g)) &&
        IsSameChain(x.tail,g[1..])
}
