// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

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

// Instances of the class BSTNode are nodes in a binary tree.
// A consequence of this definition is that all possible
// binary trees are either null or constructed by
//   new BSTNode(left,val,right)
// where left and right are legal binary trees and val is
// an int value.
//
// Note that it is not possible to change the contents of
// a binary tree.
//
// This clas definition corresponds directly with the Dafny
// definition
//    datatype BST = BSTEmpty | BSTNode(BST,int,BST)

// All values of type BSTNode are legal finite and unmodifiable
// binary trees due to the fact that it is not possible to
// change the contents of an object of type BSTNode.
//
// An empty tree is denoted by null.
//
// If the values in the binary tree are in ascending order
// when the tree is traversed inorder then the binary tree
// is considered to be a binary search tree.
public class BSTNode
{
    private final int val;
    private final BSTNode left;
    private final BSTNode right;
    
    // Notkun: BSTNode t = new BSTNode(left,val,right);
    // Fyrir:  left og right eru BSTNode (mega vera null),
    //         val er int. (Allt er þetta sjálfgefið og
    //         þarf ekki að taka fram.)
    // Eftir:  t vísar á nyjan hnút sem hefur val sem gildi,
    //         left sem vinstra undirtré og right sem
    //         hægra undirtré.

    // Usage:  BSTNode t = new BSTNode(left,val,right);
    // Pre:    left and right are BSTNode (may be null),
    //         val is an int. (All of this is a consequence
    //         of the constructor header and need not be stated.)
    // Post:   t refers to a new node that has val as its value,
    //         left as the left subtree, and right as the right
    //         subtree.
    public BSTNode( BSTNode left, int val, BSTNode right )
    {
        this.left = left;
        this.val = val;
        this.right = right;
    }

    // Notkun: int x = BSTNode.rootValue(t);
    // Fyrir:  t != null.
    // Eftir:  x er gildið í rót t.

    // Usage:  int x = BSTNode.rootValue(t);
    // Pre:    t != null.
    // Post:   x is the value in the root of t.
    public static int rootValue( BSTNode t )
    {
        return t.val;
    }

    // Notkun: BSTNode x = BSTNode.left(t);
    // Fyrir:  t != null.
    // Eftir:  x er vinstra undirtré rótar t.

    // Usage:  BSTNode x = BSTNode.left(t);
    // Pre:    t != null.
    // Post:   x is the left subtree of t.
    public static BSTNode left( BSTNode t )
    {
        return t.left;
    }

    // Notkun: BSTNode x = BSTNode.right(t);
    // Fyrir:  t != null.
    // Eftir:  x er hægra undirtré rótar t.

    // Usage:  BSTNode x = BSTNode.right(t);
    // Pre:    t != null.
    // Post:   x is the right subtree of t.
    public static BSTNode right( BSTNode t )
    {
        return t.right;
    }
}