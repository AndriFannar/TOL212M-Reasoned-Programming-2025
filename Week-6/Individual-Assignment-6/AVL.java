// Höfundur/Author: Snorri Agnarsson, snorri@hi.is

// Hlutir af tagi AVL eru hnútar í AVL tré af sambærilegum
// hlutum.
// Tilvísun í hlut af tagi AVL getur því staðið fyrir heilt
// AVL tré.
// Takið eftir því að einu opinberu aðgerðirnar eru static
// aðferðir sem eiga að viðhalda löglegu ástandi gagna.

// Objects of type AVL are nodes in an AVL tree of comparable
// objects.
// A reference to an object of type AVL can therefore denote
// a complete AVL tree.
// Note that the only public operations are static methods
// that are intended to maintain the data in a legal state.

class AVL<T extends Comparable<? super T>>
{
    private T value;
    private int height;
    private AVL<T> left;
    private AVL<T> right;

    //    AVL tré er tilvísun á hlut af þessu tagi.
    //    Til þess að slík tilvísun teljist vera AVL
    //    tré þarf hins vegar meira til.
    //    Tóm tilvísun (null) stendur fyrir tómt tré.
    //    Ef tilvísunin er ekki tóm vísar hún á hlut
    //    sem stendur fyrir rót trésins.
    //    Til þess að tréð teljist vera AVL tré þarf tréð
    //    að uppfylla annars vegar tvíleitartrjáaskilyrði:
    //       Öll gildi í vinstra undirtré eru alltaf (fyrir
    //       öll undirtré) <= rótargildi og öll gildi í
    //       hægra undirtré eru >= rótargildi.
    //    Og hins vegar AVL skilyrði:
    //       Tilviksbreytan height inniheldur hæð
    //       heildartrésins og mismunur hæða vinstri og
    //       hægri undirtrjáa er í mesta lagi 1.
    //    Hæð tóms trés (null) er skilgreint sem 0.
    
    // Til þess að aðgerðirnar á AVL tré virki þarf að
    // sjá til þess að engin tvö AVL tré sem gerðar eru
    // breytingar á hafi sameiginlega hnúta. Ef við
    // vildum losna við það skilyrði þyrftum við að
    // breyta öllum þeim aðgerðum þar sem innihaldi
    // hnúta er breytt og úthluta þess í stað nýjum
    // hnútum í hvert skipti sem við viljum færa
    // gildi frá einum hluta trésins til annars.
    
    //    An AVL tree is a reference to an object of this type.
    //    In order for this reference to be considered an AVL
    //    tree, we, however, need more.
    //    An empty reference (null) denotes an empty tree.
    //    Is the reference is not empty it refers to an object
    //    that is the root of the tree.
    //    For the tree to be considered an AVL tree the tree
    //    must on one hand fulfil the binary search tree condition:
    //       All values in the left subtree are always (for all
    //       subtrees) <= the root value and all values in the
    //       right subtree are >= the root value.
    //    An on the other hand fulfil the AVL condition:
    //       The instance variable height contains the height of
    //       the total tree and the difference between the heights
    //       of each left subtree and the right subtree is at most 1.
    //    The height of an empty tree (null) is defined as 0.
    
    // In order for the operations on AVL trees to work
    // we must ensure that no two AVL trees that are
    // modified have common nodes. if we wish to get
    // rid of that condition we must not modify the
    // contents of any existing nodes but rather
    // construct new nodes each time we make modifications.

    // Notkun: tree = new AVL(value);
    // Fyrir:  value er af tagi T, ekki null.
    // Eftir:  tree vísar á eins hnúts AVL tré með gildið value í rótinni

    // Usage:  tree = new AVL(value);
    // Pre:    value is of type T, not null.
    // Post:   tree refers to a one node AVL tree with value in the root
    public AVL( T value )
    {
        this.value = value;
        height = 1;
    }
    
    // Notkun: T x = AVL.rootValue(tree);
    // Fyrir:  tree er AVL tré, ekki tómt.
    // Eftir:  x er gildið í rót tree.

    // Usage:  T x = AVL.rootValue(tree);
    // Pre:    tree is an AVL tree, not empty.
    // Post:   x is the root value of tree.
    public static<T extends Comparable<? super T>> T rootValue( AVL<T> tree )
    {
        return tree.value;
    }

    // Notkun: AVL<T> l = AVL.left(tree);
    // Fyrir:  tree er AVL tré, ekki tómt.
    // Eftir:  l er vinstra undirtré tree.
    
    // Usage:  AVL<T> l = AVL.left(tree);
    // Pre:    tree is an AVL tré, not empty.
    // Post:   l is the left subtree of tree.
    public static<T extends Comparable<? super T>> AVL<T> left( AVL<T> tree )
    {
        return tree.left;
    }

    // Notkun: AVL<T> r = AVL.right(tree);
    // Fyrir:  tree er AVL tré, ekki tómt.
    // Eftir:  r er hægra undirtré tree.

    // Usage:  AVL<T> r = AVL.right(tree);
    // Pre:    tree is an AVL tree, not empty.
    // Post:   r is the right subtree of tree.
    public static<T extends Comparable<? super T>> AVL<T> right( AVL<T> tree )
    {
        return tree.right;
    }

    // Notkun: h = AVL.height(tree);
    // Fyrir:  tree er AVL tré, má vera tómt.
    // Eftir:  h er hæð AVL trésins tree.

    // Usage:  h = AVL.height(tree);
    // Pre:    tree is an AVL tree, may be empty.
    // Post:   h is the heught of the AVL tree tree.
    public static<T extends Comparable<? super T>> int height( AVL<T> tree )
    {
        if( tree==null ) return 0;
        return tree.height;
    }
    
    // Notkun: h = AVL.height(left,right);
    // Fyrir:  left og right eru AVL tré, mega vera tóm.
    // Eftir:  h er hæð trés með vinstri hluta left og hægri hluta right

    // Usage:  h = AVL.height(left,right);
    // Pre:    left and right are AVL tres, may be empty.
    // Post:   h is the height of a tree with the left subtree left and the right subtree right.
    public static<T extends Comparable<? super T>> int height( AVL<T> left, AVL<T> right )
    {
        int leftheight = height(left);
        int rightheight = height(right);
        if( leftheight > rightheight )
            return leftheight+1;
        else
            return rightheight+1;
    }
    
    // Notkun: f = AVL.find(tree,val);
    // Fyrir:  tree er AVL tré, val er af tagi T. val er ekki null.
    // Eftir:  f er satt ef og a[eins ef val er til í tree.

    // Usage:  f = AVL.find(tree,val);
    // Pre:    tree is an AVL tree, val is an object of type T. val is not null.
    // Post:   f is true if and only if val exists in tree.
    public static<T extends Comparable<? super T>> boolean find( AVL<T> tree, T val )
    {
        if( tree==null )
            return false;
        if( tree.value.equals(val) )
            return true;
        if( val.compareTo(tree.value) < 0 )
            return find(tree.left,val);
        else
            return find(tree.right,val);
    }
    
    // Notkun: tree = AVL.insert(org,value);
    // Fyrir:  org er AVL tré, value er hutur af tagi T, ekki null.
    // Eftir:  tree er nýja AVL tréð sem út kemur þegar hnúti með gildinu
    //         value er bætt í org tréð.
    // Ath.:   Þetta fall gerir breytingar á innihaldi hnúta í org trénu
    //         og ekki er víst að org tréð sé í löglegu ástandi eftir
    //         aðgerðina.

    // Usage:  tree = AVL.insert(org,value);
    // Pre:    org is an AVL tree, value is an object of type T, not null.
    // Post:   tree is the new AVL tree that results from adding a node with
    //         the given value into the org tree.
    // Note:   This method modifies the contents of nodes in the org tree
    //         and it is not certain that the org tree is in a legal state
    //         after the operation.
    public static<T extends Comparable<? super T>> AVL<T> insert( AVL<T> org, T value )
    {
        if( org==null )
            return new AVL<T>(value);
        if( value.compareTo(org.value) < 0 )
        {
            org.left = insert(org.left,value);
            org.height = height(org.left,org.right);
            if( org.left.height > height(org.right)+1 )
                if( height(org.left.left) >= height(org.left.right) )
                    org = rotateLeftUp(org);
                else
                    org = rotateLeftRightUp(org);
        }
        else
        {
            org.right = insert(org.right,value);
            org.height = height(org.left,org.right);
            if( org.right.height > height(org.left)+1 )
                if( height(org.right.right) >= height(org.right.left) )
                    org = rotateRightUp(org);
                else
                    org = rotateRightLeftUp(org);
        }
        return org;
    }
    
    // Notkun: s = AVL.min(tree);
    // Fyrir:  tree er ekki-tómt AVL tré
    // Eftir:  s er minnsta (fremsta) gildi í tree.

    // Usage:  s = AVL.min(tree);
    // Pre:    tree is a non-empty AVL tree.
    // Post:   s is the smallest (leftmost) value in tree.
    public static<T extends Comparable<? super T>> T min( AVL<T> tree )
    {
        if( tree.left==null ) return tree.value;
        return min(tree.left);
    }
    
    // Notkun: s = AVL.max(tree);
    // Fyrir:  tree er ekki-tómt AVL tré
    // Eftir:  s er stærsta (aftasta) gildi í tree.

    // Usage:  s = AVL.max(tree);
    // Pre:    tree is a non-empty AVL tree.
    // Post:   s is the largest (rightmost) value in tree.
    public static<T extends Comparable<? super T>> T max( AVL<T> tree )
    {
        if( tree.right==null ) return tree.value;
        return max(tree.right);
    }
    
    // Notkun: tree = AVL.delete(org,value);
    // Fyrir:  org er AVL tré, value er af tagi T, value er ekki null.
    // Eftir:  tree er nýja AVL tréð sem út kemur þegar hnúti með gildinu
    //         value er eytt í org trénu (ef einhver slíkur hnútur er til,
    //         annars er tree sama tré og org).
    // Ath.:   Þetta fall gerir breytingar á innihaldi hnúta í org trénu
    //         og ekki er víst að org tréð sé í löglegu ástandi eftir
    //         aðgerðina.

    // Usage:  tree = AVL.delete(org,value);
    // Pre:    org er AVL tré, value er af tagi T, value is not null.
    // Post:   tree is the new AVL tree that results from deleting a node
    //         with the given value from the org tree (if such a node exists,
    //         otherwise tree is the same as org).
    // Note:   This method modifies the contents of nodes in the org tree
    //         and it is not certain that the org tree is in a legal state
    //         after the operation.
    public static<T extends Comparable<? super T>> AVL<T> delete( AVL<T> org, T val )
    {
        if( org==null ) return null;
        if( val.equals(org.value) )
        {
            if( height(org.left) > height(org.right) )
            {
                org.value = max(org.left);
                org.left = delete(org.left,org.value);
                org.height = height(org.left,org.right);
                return org;
            }
            else if( org.right != null )
            {
                org.value = min(org.right);
                org.right = delete(org.right,org.value);
                org.height = height(org.left,org.right);
                return org;
            }
            else
                return null;
        }
        if( val.compareTo(org.value) < 0 )
        {
            org.left = delete(org.left,val);
            org.height = height(org.left,org.right);
            if( height(org.left) == height(org.right)-2 )
                if( height(org.right.left) > height(org.right.right) )
                    org = rotateRightLeftUp(org);
                else
                    org = rotateRightUp(org);
        }
        else
        {
            org.right = delete(org.right,val);
            org.height = height(org.left,org.right);
            if( height(org.right) == height(org.left)-2 )
                if( height(org.left.right) > height(org.left.left) )
                    org = rotateLeftRightUp(org);
                else
                    org = rotateLeftUp(org);
        }
        return org;
    }
    
    // Notkun: tree = rotateLeftUp(tree);
    // Fyrir:  tree hefur rót og vinstra barn.
    // Eftir:  Búið er að snúa tré og uppfæra hæðir miðað
    //         við eftirfarandi mynd og skila tilvísun á
    //         nýju rótina.
    //                     x            y
    //                    / \          / \
    //                   y   C  =>    A   x
    //                  / \              / \
    //                 A   B            B   C

    // Usage:  tree = rotateLeftUp(tree);
    // Pre:    tree has a root and a left child.
    // Post:   The tree has been rotated and heights have
    //         been updated according to the above figure
    //         and a reference to the new root has been returned.
    //                     x            y
    //                    / \          / \
    //                   y   C  =>    A   x
    //                  / \              / \
    //                 A   B            B   C
    private static<T extends Comparable<? super T>> AVL<T> rotateLeftUp( AVL<T> tree )
    {
        AVL<T> x=tree, y=x.left, A=y.left, B=y.right, C=x.right;
        x.left = B; x.right = C; x.height = height(B,C);
        y.left = A; y.right = x; y.height = height(A,x);
        return y;
    }
    
    // Notkun: tree = rotateRightUp(tree);
    // Fyrir:  tree hefur rót og hægra barn
    // Eftir:  Búið er að snúa tré og uppfæra hæðir miðað
    //         við eftirfarandi mynd og skila tilvísun á
    //         nýju rótina.
    //                  x              y
    //                 / \            / \
    //                A   y   =>     x   C
    //                   / \        / \
    //                  B   C      A   B
    // Usage:  tree = rotateRightUp(tree);
    // Pre:    tree has a root and a right child.
    // Post:   The tree has been rotated and heights have
    //         been updated according to the above figure
    //         and a reference to the new root has been returned.
    private static<T extends Comparable<? super T>> AVL<T> rotateRightUp( AVL<T> tree )
    {
        AVL<T> x=tree, y=x.right, A=x.left, B=y.left, C=y.right;
        x.left = A; x.right = B; x.height = height(A,B);
        y.left = x; y.right = C; y.height = height(x,C);
        return y;
    }
    
    // Notkun: tree = rotateLeftRightUp(tree);
    // Fyrir:  tree hefur rót og vinstra barn og vinstra
    //         barn hefur hægra barn.
    // Eftir:  Búið er að snúa tré og uppfæra hæðir miðað
    //         við eftirfarandi mynd og skila tilvísun á
    //         nýju rótina.
    //                     x            z
    //                    / \          / \
    //                   y   D  =>    /   \
    //                  / \          y     x
    //                 A   z        / \   / \
    //                    / \      A   B C   D
    //                   B   C
    // Usage:  tree = rotateLeftRightUp(tree);
    // Pre:    tree has a root and a left child and the left child
    //         has a right child.
    // Post:   The tree has been rotated and heights have
    //         been updated according to the above figure
    //         and a reference to the new root has been returned.
    private static<T extends Comparable<? super T>> AVL<T> rotateLeftRightUp( AVL<T> tree )
    {
        AVL<T> x=tree, y=x.left, z=y.right, A=y.left, B=z.left, C=z.right, D=x.right;
        x.left = C; x.right = D; x.height = height(C,D);
        y.left = A; y.right = B; y.height = height(A,B);
        z.left = y; z.right = x; z.height = height(x,y);
        return z;
    }

    // Notkun: tree = rotateRightLeftUp(tree);
    // Fyrir:  tree hefur rót og hægra barn og hægra
    //         barn hefur vinstra barn.
    // Eftir:  Búið er að snúa tré og uppfæra hæðir miðað
    //         við eftirfarandi mynd og skila tilvísun á
    //         nýju rótina.
    //                     x              z
    //                    / \            / \
    //                   A   y    =>    /   \
    //                      / \        x     y
    //                     z   D      / \   / \
    //                    / \        A   B C   D
    //                   B   C
    // Usage:  tree = rotateRightLeftUp(tree);
    // Pre:    tree has a root and a right child and the right child
    //         has a left child.
    // Post:   The tree has been rotated and heights have
    //         been updated according to the above figure
    //         and a reference to the new root has been returned.
    private static<T extends Comparable<? super T>> AVL<T> rotateRightLeftUp( AVL<T> tree )
    {
        AVL<T> x=tree, y=x.right, z=y.left, A=x.left, B=z.left, C=z.right, D=y.right;
        x.left = A; x.right = B; x.height = height(A,B);
        y.left = C; y.right = D; y.height = height(C,D);
        z.left = x; z.right = y; z.height = height(x,y);
        return z;
    }
}
