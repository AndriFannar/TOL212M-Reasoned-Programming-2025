// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

public class H6
{
    // Notkun: BSTNode s = insertBST(t,x);
    // Fyrir:  t er tvíleitartré, x er heiltala.
    // Eftir:  s er tvíleitartré sem inniheldur hnúta sem
    //         hafa sömu gildi og hnútarnir í t og auk þess
    //         hnút sem inniheldur gildið x.
    //         s inniheldur því einum hnút fleiri en t og
    //         einum fleiri hnúta sem innihalda gildið x.

    // Usage:  BSTNode s = H6.insertBST(t,x);
    // Pre:    t is a binary search tree, x is an int.
    // Post:   s is a binary search tree that contains nodes
    //         which have the same values as t and in
    //         addition contains a node which contains the
    //         value x. s therefore contains one more node
    //         than t does and one more node containing
    //         the value x.
    public static BSTNode insertBST( BSTNode t, int x )
    {
        if( t == null ) { return new BSTNode(null,x,null); }
        int val = BSTNode.rootValue(t);
        BSTNode left = BSTNode.left(t);
        BSTNode right = BSTNode.right(t);
        if( x < val )
            return new BSTNode(insertBST(left,x),val,right);
        else
            return new BSTNode(left,val,insertBST(right,x));
    }
    
    // Notkun: int x = maxInBST(t);
    // Fyrir:  t er tvíleitartré, ekki tómt.
    // Eftir:  x er stærsta gildið í t.

    // Usage:  int x = maxInBST(t);
    // Pre:    t is a binary search tree, not empty.
    // Post:   x is the biggest value in t.
    public static int maxInBST( BSTNode t )
    {
        while( BSTNode.right(t) != null )
            // Fastayrðing lykkju:
            //  Núverandi t er undirtré í upphaflega
            //  t sem inniheldur stærsta gildið í
            //  upphaflega t.
            // Loop invariant:
            //  the current t is a subtree in the original
            //  t which contains the biggest value in the
            //  original t.
            t = BSTNode.right(t);
        return BSTNode.rootValue(t);
    }
    
    // Notkun: BSNNode s = deleteBST(t,x);
    // Fyrir:  t er tvíleitartré.
    // Eftir:  s er tvíleitartré og poki þeirra gilda
    //         sem eru í s er jafnt poka þeirra gilda
    //         sem eru í t, að frádregnu einu x, ef
    //         x finnst í t.

    // Usage:  BSNNode s = deleteBST(t,x);
    // Pre:    t is a binary search tree.
    // Post:   s is a binary search tree and the multiset
    //         of values that s contains is equal to the
    //         multiset of values that are in t with one
    //         x subtracted, if an x is to be found in t.
    public static BSTNode deleteBST( BSTNode t, int x )
    {
        if( t == null ) return null;
        int val = BSTNode.rootValue(t);
        BSTNode left = BSTNode.left(t);
        BSTNode right = BSTNode.right(t);
        if( x < val )
            return new BSTNode(deleteBST(left,x),val,right);
        if( x > val )
            return new BSTNode(left,val,deleteBST(right,x));
        if( left == null ) return right;
        if( right == null ) return left;
        int maxInRight = maxInBST(right);
        BSTNode newRight = deleteBST(right,maxInRight);
        return new BSTNode(left,maxInRight,newRight);
    }
    
    // Notkun: sort(a);
    // Fyrir:  a er heiltalnafylki.
    // Eftir:  a hefur verið raðað í vaxandi röð.

    // Usage:  sort(a);
    // Pre:    a is an array of int.
    // Post:   a has been sorted in ascending order.
    public static void sort( int[] a )
    {
        BSTNode t = null;
        int i = 0;
        while( i != a.length )
            // Fastayrðing lykkju:
            //   0 <= i <= a.llength.
            //   t er tvíleitartré og poki þeirra
            //   gilda sem eru í t er sama og poki
            //   þeirra gilda sem eru á svæðinu
            //   a[0..i) í fylkinu a.
            // Loop invariant:
            //   0 <= i <= a.llength.
            //   t is a binary search tree and the
            //   multiset of values that t contains
            //   is the same as the multiset of values
            //   contained in the section a[0..i) of
            //   the array a.
            t = insertBST(t,a[i++]);
        while( i != 0 )
            // Fastayrðing lykkju:
            //   0 <= i <= a.llength.
            //   t er tvíleitartré. Svæðið a[i..]
            //   inniheldur a.length-i stærstu gildin
            //   í upphaflega a í vaxandi röð.
            //   t inniheldur restina af upphaflegu
            //   gildunum í a.
            // Loop invariant:
            //   0 <= i <= a.llength.
            //   t is a binary search tree. The section
            //   a[i..] contains the a.length-i biggest
            //   values in the original a in ascending
            //   order.
            //   t contains the rest of the values in
            //   the original a.
        {
            a[--i] = maxInBST(t);
            t = deleteBST(t,a[i]);
        }
    }
    
    public static void main( String[] args )
    {
        int[] a = new int[]{0,9,1,8,2,7,3,6,4,5,10,11,12,13,19,18,17,16,15,14,0,0,0,5,5,5};
        H6.sort(a);
        for( int i=0 ; i!=a.length ; i++ )
            // Fastayrðing lykkju: Gildin í a[0],a[1],...,a[i-1] hafa verið skrifuð.
            // Loop invariant: the values in a[0],a[1],...,a[i-1] have been written.
            System.out.print(a[i]+" ");
    }
}