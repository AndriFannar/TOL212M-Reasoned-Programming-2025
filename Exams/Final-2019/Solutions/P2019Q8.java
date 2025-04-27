public class P2019Q8
{
    // Notkun: BSTNode r = searchLastLT100Recursive(t);
    // Fyrir:  t er tvíleitartré.
    // Eftir:  Ef til er hnútur í t sem inniheldur gildi
    //         sem er <100 þá vísar r á aftasta slíkan
    //         hnút í milliröð. Annars er r null.
    public static BSTNode searchLastLT100Recursive( BSTNode t )
    {
        if( t == null ) return null;
        if( BSTNode.rootValue(t) < 100 )
        {
            BSTNode r = searchLastLT100Recursive(BSTNode.right(t));
            if( r == null ) return t;
            return r;
        }
        return searchLastLT100Recursive(BSTNode.left(t));
    }
}