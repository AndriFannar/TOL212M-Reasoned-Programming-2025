datatype BST = BSTEmpty | BSTNode(BST,char,BST)
newtype dir = x | 0 <= x <= 1

predicate IsTreePath( t: BST, p: seq<dir> )
    decreases t
{
    if p == [] then
        true
    else
        match t
        case BSTEmpty =>
            false
        case BSTNode(left,val,right) =>
            if p[0] == 0 then
                IsTreePath(left,p[1..])
            else
                IsTreePath(right,p[1..])
}

predicate IsSubTree( t: BST, r: BST )
    decreases t
{
    if r == BSTEmpty then
        true
    else
        match t
        case BSTEmpty =>
            false
        case BSTNode(left,val,right) =>
            r == t || IsSubTree(left,r) || IsSubTree(right,r)
}

function Subtree( t: BST, p: seq<dir> ): BST
    decreases t
    requires IsTreePath(t,p)
    ensures Subtree(t,p) != BSTEmpty ==> IsSubTree(t,Subtree(t,p))
{
    if p == [] then
        t
    else if p[0] == 0 then
        Subtree(Left(t),p[1..])
    else
        Subtree(Right(t),p[1..])
}

function TreeSeq( t: BST ): seq<char>
    decreases t
{
    match t
    case BSTEmpty =>
        []
    case BSTNode(left,val,right) =>
        TreeSeq(left)+[val]+TreeSeq(right)
}

function PreSeq( t: BST, p: seq<dir> ): seq<char>
    decreases t
{
    if !IsTreePath(t,p) then 
        "?"
    else if p == [] then
        []
    else
        match t 
        case BSTEmpty =>
            []
        case BSTNode(left,val,right) =>
            if p[0] == 0 then
                PreSeq(left,p[1..])
            else
                TreeSeq(left)+[val]+PreSeq(right,p[1..])
}

function PostSeq( t: BST, p: seq<dir> ): seq<char>
    decreases t
{
    if !IsTreePath(t,p) then
        ['?']
    else if p == [] then
        []
    else
        match t 
        case BSTEmpty =>
            []
        case BSTNode(left,val,right) =>
            if p[0] == 1 then
                PostSeq(right,p[1..])
            else
                PostSeq(left,p[1..])+[val]+TreeSeq(right)
}

function MidSeq( t: BST, p: seq<dir> ): seq<char>
{
    if !IsTreePath(t,p) then 
        "?"
    else 
        TreeSeq(Subtree(t,p))
}

function RootValue( t: BST ): char
    requires t != BSTEmpty
{
    match t 
    case BSTNode(left,val,right) => val
}

function Left( t: BST ): BST
    requires t != BSTEmpty
{
    match t 
    case BSTNode(left,val,right) => left
}

function Right( t: BST ): BST
    requires t != BSTEmpty
{
    match t 
    case BSTNode(left,val,right) => right
}

function PreSeqExcluding( t: BST, p: seq<dir> ): seq<char>
{
    if !IsTreePath(t,p) || Subtree(t,p)==BSTEmpty then "?"
    else PreSeq(t,p)+TreeSeq(Left(Subtree(t,p)))
}

function PostSeqExcluding( t: BST, p: seq<dir> ): seq<char>
{
    if !IsTreePath(t,p) || Subtree(t,p)==BSTEmpty then "?"
    else TreeSeq(Right(Subtree(t,p)))+PostSeq(t,p)
}

function PreSeqIncluding( t: BST, p: seq<dir> ): seq<char>
{
    if !IsTreePath(t,p) || Subtree(t,p)==BSTEmpty then "?"
    else PreSeq(t,p)+TreeSeq(Left(Subtree(t,p)))+[RootValue(Subtree(t,p))]
}

function PostSeqIncluding( t: BST, p: seq<dir> ): seq<char>
{
    if !IsTreePath(t,p) || Subtree(t,p)==BSTEmpty then "?"
    else [RootValue(Subtree(t,p))]+TreeSeq(Right(Subtree(t,p)))+PostSeq(t,p)
}

function N( l: BST, c: char, r: BST): BST
{
    BSTNode(l,c,r)
}

function L( c: char ): BST
{
    BSTNode(BSTEmpty,c,BSTEmpty)
}

method Solve( t: BST, p: seq<dir> )
{
    print "PreSeq(t,";
    print p;
    print ")=";
    var s := PreSeq(t,p);
    print s;
    print "\n";
    print "MidSeq(t,";
    print p;
    print ")=";
    s := MidSeq(t,p);
    print s;
    print "\n";
    print "PostSeq(t,";
    print p;
    print ")=";
    s := PostSeq(t,p);
    print s;
    print "\n";
    print "PreSeqIncluding(t,";
    print p;
    print ")=";
    s := PreSeqIncluding(t,p);
    print s;
    print "\n";
    print "PostSeqExcluding(t,";
    print p;
    print ")=";
    s := PostSeqExcluding(t,p);
    print s;
    print "\n";
    print "PreSeqExcluding(t,";
    print p;
    print ")=";
    s := PreSeqExcluding(t,p);
    print s;
    print "\n";
    print "PostSeqIncluding(t,";
    print p;
    print ")=";
    s := PostSeqIncluding(t,p);
    print s;
    print "\n";
    print "\n";
}

method Main()
{
    var e := BSTEmpty;
    var t := N(
                N(
                    L('s'),
                    't',
                    e
                ),
                'a',
                N(
                    N(
                        N(
                            L('f'),
                            'a',
                            e
                        ),
                        'r',
                        N(
                            N(
                                L('u'),
                                'g',
                                L('l')
                            ),
                            'x',
                            L('y')
                        )
                    ),
                    'z',
                    L('w')
                )
            );
    Solve(t,[]);
    Solve(t,[0]);
    Solve(t,[1]);
    Solve(t,[1,0]);
    Solve(t,[0,0]);
    Solve(t,[0,1]);
    Solve(t,[1,1]);
    Solve(t,[0,1,1]);
    Solve(t,[1,0,0]);
    Solve(t,[1,1,0]);
    Solve(t,[0,0,0]);
    Solve(t,[0,1,0]);
    Solve(t,[0,0,1]);
    Solve(t,[1,0,1]);
    Solve(t,[1,1,1]);
    Solve(t,[1,0,1,0,1]);
    Solve(t,[1,0,1,0,1,0]);
    Solve(t,[1,0,1,0,1,1]);
    Solve(t,[1,0,1,0,0]);
    Solve(t,[1,0,1,0,0,0]);
}