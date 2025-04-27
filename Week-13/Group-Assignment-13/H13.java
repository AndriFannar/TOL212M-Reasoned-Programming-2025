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
        ???
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
        ???
    }

    // Notkun: x = max(t);
    // Fyrir:  t er tvíleitartré, ekki tómt.
    // Eftir:  x er stærsta gildið í t.

    // Usage:  x = max(t);
    // Pre:    t is a non-empty binary search tree.
    // Post:   x is the biggest value in t.
    public static int max( BSTNode t )
    {
        // Munið að ef þið notið lykkju hér þá
        // þarf hún fastayrðingu.
        // Remember that if you use a loop then
        // it needs a loop invariant.
        ???
    }
}