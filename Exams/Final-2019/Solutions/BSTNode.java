// Höfundur: Snorri Agnarsson, snorri@hi.is

// Tilvik af klasanum BSTNode eru hnútar í tvíundartré.
// Afleiðing af þessari skilgreiningu er að öll möguleg
// tvíundartré eru annaðhvort null eða smíðuð með
//   new BSTNode(left,val,right)
// þar sem left og right eru lögleg tvíundartré og val
// er heiltölugildi.
//
// Athugið að ekki er mögulegt að breyta innihaldi
// tvíundartrés.
//
// Þessi klasaskilgreining er bein samsvörun við Dafny
// skilgreininguna
//    datatype BST = BSTEmpty | BSTNode(BST,int,BST)

// Öll gildi af tagi BSTNode eru lögleg, endanleg og
// óbreytanleg tvíundartré, sem helgast af því að ekki
// er hægt að breyta innihaldi hlutar af tagi BSTNode.
//
// Tómt tré er táknað með null.
//
// Ef gildin í tvíundartrénu eru í vaxandi röð þegar
// ferðast er gegnum tréð í milliröð (inorder röð)
// þá telst tréð vera tvíleitartré (binary search tree).

public class BSTNode
{
    private int val;
    private BSTNode left;
    private BSTNode right;
    
    // Notkun: BSTNode t = new BSTNode(left,val,right);
    // Fyrir:  left og right eru BSTNode (mega vera null),
    //         val er int. (Allt er þetta sjálfgefið og
    //         þarf ekki að taka fram.)
    // Eftir:  t vísar á hnút sem hefur val sem gildi,
    //         left sem vinstra undirtré og right sem
    //         hægra undirtré.
    public BSTNode( BSTNode left, int val, BSTNode right )
    {
        this.left = left;
        this.val = val;
        this.right = right;
    }

    // Notkun: int x = BSTNode.rootValue(t);
    // Fyrir:  t != null.
    // Eftir:  x er gildið í rót t.
    public static int rootValue( BSTNode t )
    {
        return t.val;
    }

    // Notkun: BSTNode x = BSTNode.left(t);
    // Fyrir:  t != null.
    // Eftir:  x er vinstra undirtré rótar t.
    public static BSTNode left( BSTNode t )
    {
        return t.left;
    }

    // Notkun: BSTNode x = BSTNode.right(t);
    // Fyrir:  t != null.
    // Eftir:  x er hægra undirtré rótar t.
    public static BSTNode right( BSTNode t )
    {
        return t.right;
    }
}