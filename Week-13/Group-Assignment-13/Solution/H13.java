public class H13
{
    // Notkun: t2 = insert(t1,x);
    // Fyrir:  t1 er tvíleitartré, x er heiltala
    // Eftir:  t2 er tvíleitartré sem inniheldur
    //         öll heiltölugildin í t1 ásamt x.

    // Usage:  t2 = insert(t1,x);
    // Pre:    t1 is a binary search tree, x is an int
    // Post:   t2 is a binary search tree that contains
    //         all the int values in t1, with x added.
    public static BSTNode insert( BSTNode t, int x )
    {
        if( t == null ) return new BSTNode(null,x,null);
        if( x < BSTNode.rootValue(t) )
            return
                new BSTNode ( insert(BSTNode.left(t),x)
                            , BSTNode.rootValue(t)
                            , BSTNode.right(t)
                            );
        else
            return
                new BSTNode ( BSTNode.left(t)
                            , BSTNode.rootValue(t)
                            , insert(BSTNode.right(t),x)
                            );
    }

    // Notkun: t2 = delete(t1,x);
    // Fyrir:  t1 er tvíleitartré, x er heiltala
    // Eftir:  t2 er tvíleitartré sem inniheldur
    //         öll heiltölugildin í t1 nema hvað
    //         eitt x hefur verið fjarlægt ef það
    //         var til staðar.

    // Usage:  t2 = delete(t1,x);
    // Pre:    t1 is a binary search tree, x is an int
    // Post:   t2 is a binary search tree that contains
    //         all the int values in t1, except that
    //         one x has been removed, if it existed in t1.
    public static BSTNode delete( BSTNode t, int x )
    {
        if( t == null ) return null;
        if( x < BSTNode.rootValue(t) )
            return
                new BSTNode ( delete(BSTNode.left(t),x)
                            , BSTNode.rootValue(t)
                            , BSTNode.right(t)
                            );
        if( x > BSTNode.rootValue(t) )
            return
                new BSTNode ( BSTNode.left(t)
                            , BSTNode.rootValue(t)
                            , delete(BSTNode.right(t),x)
                            );
        if( BSTNode.left(t) == null )
            return BSTNode.right(t);
        if( BSTNode.right(t) == null )
            return BSTNode.left(t);
        int m = max(BSTNode.left(t));
        return
            new BSTNode ( delete(BSTNode.left(t),m)
                        , m
                        , BSTNode.right(t)
                        );
    }

    // Notkun: x = max(t);
    // Fyrir:  t er tvíleitartré, ekki tómt.
    // Eftir:  x er stærsta gildið í t.

    // Usage:  x = max(t);
    // Pre:    t is a non-empty binary search tree.
    // Post:   x is the biggest value in t.
    public static int max( BSTNode t )
    {
        if( BSTNode.right(t) == null )
            return BSTNode.rootValue(t);
        return max(BSTNode.right(t));
    }
    
    // Notkun: java H13 i1 i2 ... iN
    // Fyrir:  i1, i2, ..., iN eru heiltölur
    // Eftir:  Búið er að skrifa tölurnar í
    //         minnkandi röð á aðalúttak.

    // Usage:  java H13 i1 i2 ... iN
    // Pre:    i1, i2, ..., iN eru heiltölur
    // Post:   The numbers have been written in
    //         descending order to stdout.
    public static void main( String[] args )
    {
        BSTNode t = null;
        for( int i=0 ; i!=args.length ; i++ )
            // t er tvíleitartré sem inniheldur
            // tölurnar úr args[0..i).
            // t is a binary search tree that
            // contains the numbers from a[0..i).
            t = insert(t,Integer.parseInt(args[i]));
        while( t != null )
            // Búið er að skrifa núll eða fleiri
            // stærstu tölurnar í minnkandi röð.
            // t er tvíleitartré sem inniheldur
            // afganginn af tölunum.
            // Zero or more of the biggest numbers
            // have been written in descending order
            // to stdout. The rest are in the binary
            // search tree t.
        {
            int m = max(t);
            System.out.print(m+" ");
            t = delete(t,m);
        }
    }
}