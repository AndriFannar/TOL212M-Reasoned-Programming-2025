/*
AVL trees in Dafny.
Written by Snorri Agnarsson, snorri@hi.is.
May 2018.
*/

datatype AVLTree = EmptyAVL | RootedAVL(int,AVLTree,int,AVLTree)

function AVLContentSeq( t: AVLTree ): seq<int>
	ensures t!=EmptyAVL ==> AVLContentSeq(t)==AVLContentSeq(LeftTree(t))+[RootValue(t)]+AVLContentSeq(RightTree(t))
{
	match t
	case EmptyAVL => []
	case RootedAVL(h,left,x,right) => AVLContentSeq(left)+[x]+AVLContentSeq(right)
}

function LeftTree( t: AVLTree ): AVLTree
	ensures AVLContentMultiset(LeftTree(t)) <= AVLContentMultiset(t)
	ensures IsValidAVL(t) ==> IsValidAVL(LeftTree(t))
{
	match t
	case EmptyAVL => EmptyAVL
	case RootedAVL(h,left,x,right) => left
}

function RightTree( t: AVLTree ): AVLTree
	ensures AVLContentMultiset(RightTree(t)) <= AVLContentMultiset(t)
	ensures IsValidAVL(t) ==> IsValidAVL(RightTree(t))
{
	match t
	case EmptyAVL => EmptyAVL
	case RootedAVL(h,left,x,right) => right
}

function RootValue( t: AVLTree ): int
	requires t!=EmptyAVL
{
	match t
	case RootedAVL(h,left,x,right) => x
}

function AVLContentMultiset( t: AVLTree ): multiset<int>
	decreases t
{
	match t
	case EmptyAVL => multiset{}
	case RootedAVL(h,left,x,right) =>
			AVLContentMultiset(left)+multiset{x}+AVLContentMultiset(right)
}

predicate IsAVLSorted( t: AVLTree )
	decreases t
{
	match t
	case EmptyAVL => true
	case RootedAVL(h,left,x,right) =>
			IsAVLSorted(left) &&
			IsAVLSorted(right) && 
			(forall u:: u in AVLContentMultiset(left) ==> u<=x) && 
			(forall u:: u in AVLContentMultiset(right) ==> u>=x)
}

function AVLHeight( t: AVLTree) : int
{
	match t
	case EmptyAVL => 0
	case RootedAVL(h,left,x,right) => h
}

lemma LemmaValidHasHeight( t: AVLTree )
	requires IsValidAVL(t)
	ensures AVLHeight(t)>=0
{}

function max( x: int, y: int ): int
	ensures max(x,y)>=x
	ensures max(x,y)>=y
	ensures max(x,y)==x || max(x,y)==y
{
	if x<y then y else x
}

predicate IsValidAVL( t: AVLTree )
	decreases t
{
	match t
	case EmptyAVL => true
	case RootedAVL(h,left,x,right) =>
			IsAVLSorted(t) &&
			IsValidAVL(left) &&
			IsValidAVL(right) &&
			h==1+max(AVLHeight(left),AVLHeight(right)) &&
			AVLHeight(left)-1<=AVLHeight(right)<=AVLHeight(left)+1
}


function ConstructAVL( A: AVLTree, x: int, B: AVLTree ): AVLTree
	requires forall z:: z in AVLContentMultiset(A) ==> z <= x
	requires forall z:: z in AVLContentMultiset(B) ==> z >= x
	requires (AVLHeight(A)-1 <= AVLHeight(B) <= AVLHeight(A)+1) || (AVLHeight(B)-1 <= AVLHeight(A) <= AVLHeight(B)+1)
	requires IsValidAVL(A)
	requires IsValidAVL(B)
	ensures (AVLHeight(A)-1 <= AVLHeight(B) <= AVLHeight(A)+1) && (AVLHeight(B)-1 <= AVLHeight(A) <= AVLHeight(B)+1)
	ensures AVLHeight(ConstructAVL(A,x,B)) == 1+max(AVLHeight(A),AVLHeight(B))
	ensures AVLContentMultiset(ConstructAVL(A,x,B)) == AVLContentMultiset(A)+multiset{x}+AVLContentMultiset(B)
	ensures AVLContentSeq(ConstructAVL(A,x,B)) == AVLContentSeq(A)+[x]+AVLContentSeq(B)
	ensures ConstructAVL(A,x,B) == RootedAVL(1+max(AVLHeight(A),AVLHeight(B)),A,x,B)
	ensures IsAVLSorted(ConstructAVL(A,x,B))
	ensures IsValidAVL(ConstructAVL(A,x,B))
{
	RootedAVL(1+max(AVLHeight(A),AVLHeight(B)),A,x,B)
}

method AVLMax( t: AVLTree ) returns (res: int)
	decreases TreeSize(t)
	requires IsValidAVL(t)
	requires t!=EmptyAVL
	ensures res in AVLContentMultiset(t)
	ensures forall u:: u in AVLContentMultiset(t) ==> u<=res
{
	match t
	case RootedAVL(h,left,u,right) =>
	{
		if right==EmptyAVL { return u; }
		res := AVLMax(right);
	}
}

method AVLMinLoop( t: AVLTree ) returns (res: int)
	requires IsValidAVL(t)
	requires t!=EmptyAVL
	ensures res in AVLContentMultiset(t)
	ensures forall u:: u in AVLContentMultiset(t) ==> u>=res
{
	var vart: AVLTree;
	vart := t;
	ghost var rightset: multiset<int> := multiset{};
	while LeftTree(vart) != EmptyAVL
		decreases TreeSize(vart)
		invariant IsValidAVL(vart)
		invariant vart != EmptyAVL
		invariant AVLContentMultiset(vart)+rightset == AVLContentMultiset(t)
		invariant forall u:: u in rightset ==> u >= RootValue(vart)
	{
		ghost var oldrightset := rightset;
		ghost var oldvart := vart;
		rightset := multiset{RootValue(vart)}+AVLContentMultiset(RightTree(vart))+rightset;
		vart := LeftTree(vart);
		AssociateUnion4(AVLContentMultiset(RightTree(oldvart)),multiset{RootValue(oldvart)},AVLContentMultiset(LeftTree(oldvart)),oldrightset);
		calc ==
		{
			AVLContentMultiset(vart)+rightset;
			AVLContentMultiset(LeftTree(oldvart))+rightset;
			AVLContentMultiset(LeftTree(oldvart))+multiset{RootValue(oldvart)}+AVLContentMultiset(RightTree(oldvart))+oldrightset;
		}
		assert AVLContentMultiset(vart)+rightset == AVLContentMultiset(oldvart)+oldrightset;
		assert RootValue(vart) in AVLContentMultiset(vart);
		assert RootValue(vart) <= RootValue(oldvart);
		assert forall u:: u in rightset ==> u >= RootValue(vart);
	}
	res := RootValue(vart);
	AssociateUnion4(AVLContentMultiset(LeftTree(vart)),multiset{RootValue(vart)},AVLContentMultiset(RightTree(vart)),rightset);
	UnionWithEmpty(multiset{RootValue(vart)}+AVLContentMultiset(LeftTree(vart))+rightset);
	calc ==
	{
		AVLContentMultiset(t);
		AVLContentMultiset(vart)+rightset;
		AVLContentMultiset(LeftTree(vart))+multiset{RootValue(vart)}+AVLContentMultiset(RightTree(vart))+rightset;
		AVLContentMultiset(LeftTree(vart))+(multiset{RootValue(vart)}+AVLContentMultiset(RightTree(vart))+rightset);
		calc ==
		{
			AVLContentMultiset(LeftTree(vart));
			multiset{};
		}
		multiset{}+(multiset{RootValue(vart)}+AVLContentMultiset(RightTree(vart))+rightset);
		multiset{RootValue(vart)}+AVLContentMultiset(RightTree(vart))+rightset;
	}
	assert AVLContentMultiset(t) == multiset{RootValue(vart)}+AVLContentMultiset(RightTree(vart))+rightset;
	assert forall u:: u in AVLContentMultiset(t) ==> u>=res;
}

method AVLMaxLoop( t: AVLTree ) returns (res: int)
	requires IsValidAVL(t)
	requires t!=EmptyAVL
	ensures res in AVLContentMultiset(t)
	ensures forall u:: u in AVLContentMultiset(t) ==> u<=res
{
	var vart: AVLTree;
	vart := t;
	ghost var leftset: multiset<int>;
	leftset := multiset{};
	while RightTree(vart) != EmptyAVL
		decreases TreeSize(vart)
		invariant IsValidAVL(vart)
		invariant vart != EmptyAVL
		invariant leftset+AVLContentMultiset(vart) == AVLContentMultiset(t)
		invariant forall u:: u in leftset ==> u <= RootValue(vart)
	{
		ghost var oldleftset := leftset;
		ghost var oldvart := vart;
		leftset := leftset+AVLContentMultiset(LeftTree(vart))+multiset{RootValue(vart)};
		vart := RightTree(vart);
		AssociateUnion4(oldleftset,AVLContentMultiset(LeftTree(oldvart)),multiset{RootValue(oldvart)},AVLContentMultiset(RightTree(oldvart)));
		calc ==
		{
			leftset+AVLContentMultiset(vart);
			oldleftset+AVLContentMultiset(LeftTree(oldvart))+multiset{RootValue(oldvart)}+AVLContentMultiset(RightTree(oldvart));
			oldleftset+(AVLContentMultiset(LeftTree(oldvart))+multiset{RootValue(oldvart)}+AVLContentMultiset(RightTree(oldvart)));
			oldleftset+AVLContentMultiset(oldvart);
		}
		assert leftset+AVLContentMultiset(vart) == oldleftset+AVLContentMultiset(oldvart);
		assert RootValue(vart) in AVLContentMultiset(vart);
		assert RootValue(vart) >= RootValue(oldvart);
		assert forall u:: u in leftset ==> u <= RootValue(vart);
	}
	res := RootValue(vart);
	UnionWithEmpty(leftset+AVLContentMultiset(LeftTree(vart))+multiset{RootValue(vart)});
	calc ==
	{
		AVLContentMultiset(t);
		leftset+AVLContentMultiset(vart);
		leftset+AVLContentMultiset(LeftTree(vart))+multiset{RootValue(vart)}+AVLContentMultiset(RightTree(vart));
		calc ==
		{
			AVLContentMultiset(RightTree(vart));
			multiset{};
		}
		leftset+AVLContentMultiset(LeftTree(vart))+multiset{RootValue(vart)}+multiset{};
		leftset+AVLContentMultiset(LeftTree(vart))+multiset{RootValue(vart)};
	}
	assert AVLContentMultiset(t) == leftset+AVLContentMultiset(LeftTree(vart))+multiset{RootValue(vart)};
	assert forall u:: u in AVLContentMultiset(t) ==> u<=res;
}

lemma UnionWithEmpty( A: multiset<int> )
	ensures A+multiset{} == A == multiset{}+A
{}

lemma AssociateUnion4( A: multiset<int>, B: multiset<int>, C: multiset<int>, D: multiset<int> )
	ensures A+B+C+D == A+(B+C+D) == (A+B+C)+D
{}

method AVLMin( t: AVLTree ) returns (res: int)
	decreases TreeSize(t)
	requires IsValidAVL(t)
	requires t!=EmptyAVL
	ensures res in AVLContentMultiset(t)
	ensures forall u:: u in AVLContentMultiset(t) ==> u>=res
{
	match t
	case RootedAVL(h,left,u,right) =>
	{
		if left==EmptyAVL { return u; }
		res := AVLMin(left);
	}
}

lemma HeightLemmas( t: AVLTree )
	requires IsValidAVL(t)
	ensures AVLHeight(t)>=0
	ensures AVLHeight(t)==0 <==> t==EmptyAVL
	ensures AVLHeight(t)>1 <==> |AVLContentMultiset(t)|>1
{
}

predicate ValidSiblings( A: AVLTree, x: int, B: AVLTree )
	requires IsValidAVL(A)
	requires IsValidAVL(B)
	requires AVLHeight(A)-1 <= AVLHeight(B) <= AVLHeight(A)+1
	requires forall w:: w in AVLContentMultiset(A) ==> w <= x
	requires forall w:: w in AVLContentMultiset(B) ==> w >= x
	ensures IsValidAVL(ConstructAVL(A,x,B))
{
	true
}

method InsertIntoAVL( t: AVLTree, x: int ) returns (res: AVLTree)
	decreases TreeSize(t)
	requires IsValidAVL(t)
	ensures IsValidAVL(res)
	ensures AVLHeight(t) <= AVLHeight(res) <= AVLHeight(t)+1
	ensures AVLContentMultiset(res)==AVLContentMultiset(t)+multiset{x}
{
	res := EmptyAVL;
	if t==EmptyAVL
	{
		res := RootedAVL(1,EmptyAVL,x,EmptyAVL);
		assert AVLHeight(res)==1+AVLHeight(EmptyAVL);
		assert IsAVLSorted(res);
		assert IsValidAVL(res);
		return;
	}
	assert t != EmptyAVL;
	var left := LeftTree(t);
	var right := RightTree(t);
	var y := RootValue(t);
	if x == y
	{
		if AVLHeight(left) < AVLHeight(right)
		{
			var newLeft := InsertIntoAVL(left,x);
			assert AVLHeight(newLeft) <= AVLHeight(left)+1 == AVLHeight(right);
			res := ConstructAVL(newLeft,y,right);
			return;
		}
		var newRight := InsertIntoAVL(right,x);
		assert AVLContentMultiset(newRight) == AVLContentMultiset(right)+multiset{x};
		BothGEImpliesUnionGE1(AVLContentMultiset(right),x,AVLContentMultiset(newRight),y);
		res := ConstructAVL(left,y,newRight);
		return;
	}
	if x < y
	{
		if left==EmptyAVL
		{
			var newLeft := ConstructAVL(EmptyAVL,x,EmptyAVL);
			HeightLemmas(t);
			HeightLemmas(left);
			HeightLemmas(right);
			assert AVLHeight(newLeft)==1;
			res := ConstructAVL(newLeft,y,right);
			return;
		}
		var newLeft := InsertIntoAVL(left,x);
		BothLEImpliesUnionLE1(AVLContentMultiset(left),x,AVLContentMultiset(newLeft),y);
		if AVLHeight(right)-1<=AVLHeight(newLeft)<=AVLHeight(right)+1
		{
			assert ValidSiblings(newLeft,y,right);
			res := ConstructAVL(newLeft,y,right);
			assert IsValidAVL(res);
			assert AVLContentMultiset(res)==AVLContentMultiset(t)+multiset{x};
			return;
		}
		var A := LeftTree(newLeft);
		var z := RootValue(newLeft);
		assert AVLContentMultiset(newLeft) == AVLContentMultiset(left)+multiset{x};
		assert z in AVLContentMultiset(newLeft);
		BothLEImpliesUnionLE1(AVLContentMultiset(left),x,AVLContentMultiset(newLeft),y);
		assert z <= y;
		var X := RightTree(newLeft);
		if AVLHeight(A)>=AVLHeight(X)
		{
			//       y                      z
			//      / \                    / \
			//     z   right     ---->    A   y
			//    / \                        / \
			//   A   X                      X   right
			assert x <= y;
			assert AVLContentMultiset(newLeft) == AVLContentMultiset(left)+multiset{x};
			assert z in AVLContentMultiset(newLeft);
			assert z <= y;
			InsertionRotateRight(t,x,left,newLeft,A,z,X,y,right);
			res := ConstructAVL(A,z,ConstructAVL(X,y,right));
			return;
		}
		var B := LeftTree(X);
		var C := RightTree(X);
		assert IsValidAVL(A);
		HeightLemmas(A);
		assert AVLHeight(A) >= 0;
		assert AVLHeight(X) > AVLHeight(A) >= 0;
		HeightLemmas(X);
		assert X != EmptyAVL;
		var u := RootValue(X);
		//       y                              u
		//      / \                            / \
		//     z   D=right                    /   \
		//    / \              ---->         z     y
		//   A   u=X                        / \   / \
		//      / \                        A   B C   D
		//     B   C
		assert u in AVLContentMultiset(X);
		assert u in AVLContentMultiset(newLeft);
		assert forall w:: w in AVLContentMultiset(newLeft) ==> w <= y;
		assert z <= u <= y;
		InsertionDoubleRotateRight(t,x,left,newLeft,X,A,z,B,u,C,y,right);
		res := ConstructAVL(ConstructAVL(A,z,B),u,ConstructAVL(C,y,right));
		return;
	}
	assert x >= y;
	if right==EmptyAVL
	{
		var newRight := ConstructAVL(EmptyAVL,x,EmptyAVL);
		HeightLemmas(t);
		HeightLemmas(left);
		HeightLemmas(right);
		assert AVLHeight(newRight)==1;
		assert AVLContentMultiset(newRight) == multiset{x};
		res := ConstructAVL(left,y,newRight);
		return;
	}
	var newRight := InsertIntoAVL(right,x);
	assert AVLContentMultiset(newRight) == AVLContentMultiset(right)+multiset{x};
	BothGEImpliesUnionGE1(AVLContentMultiset(right),x,AVLContentMultiset(newRight),y);
	if AVLHeight(left)-1<=AVLHeight(newRight)<=AVLHeight(left)+1
	{
		res := ConstructAVL(left,y,newRight);
		assert AVLContentMultiset(res)==AVLContentMultiset(t)+multiset{x};
		return;
	}
	var z := RootValue(newRight);
	assert z in AVLContentMultiset(newRight);
	assert z >= y;
	var X := LeftTree(newRight);
	var D := RightTree(newRight);
	//        y
	//       / \
	// left=A   z=newRight
	//         / \
	//        X   D
	if AVLHeight(D)>=AVLHeight(X)
	{
		//        y                        z
		//       / \                      / \
		// left=A   z=newRight  ---->    y   D
		//         / \                  / \
		//      X=B   D                A   X
		assert x > y;
		InsertionRotateLeft(t,x,right,newRight,left,y,X,z,D);
		res := ConstructAVL(ConstructAVL(left,y,X),z,D);
		return;
	}
	//        y                                 u
	//       / \                               / \
	// (+2) A   z=newRight                    /   \
	//         / \           ---->           y     z
	//        u > D                         / \   / \
	//       / \                           A   B C   D
	//      B   C
	var A := left;
	var leftright := LeftTree(newRight);
	LemmaValidHasHeight(D);
	assert AVLHeight(leftright) > AVLHeight(D);
	HeightLemmas(leftright);
	var u := RootValue(leftright);
	assert u in AVLContentMultiset(leftright);
	assert u <= z;
	var B := LeftTree(leftright);
	var C := RightTree(leftright);
	//        y                                 u
	//       / \                               / \
	// (+2) A   z=newRight                    /   \
	//         / \           ---->           y     z
	//        u > D                         / \   / \
	//       / \                           A   B C   D
	//      B   C
	assert y <= u <= z;
	InsertionDoubleRotateLeft(t,x,right,newRight,leftright,left,y,B,u,C,z,D);
	res := ConstructAVL(ConstructAVL(left,y,B),u,ConstructAVL(C,z,D));
}

lemma LemmaDeleteMaxFromLeft( t: AVLTree, orgLeft: AVLTree, newLeft: AVLTree, right: AVLTree, u: int, x: int )
	requires IsValidAVL(t)
	requires IsValidAVL(orgLeft)
	requires IsValidAVL(newLeft)
	requires IsValidAVL(right)
	requires t != EmptyAVL
	requires LeftTree(t) == orgLeft
	requires RightTree(t) == right
	requires RootValue(t) == x
	requires AVLContentMultiset(orgLeft) == AVLContentMultiset(newLeft)+multiset{u}
	requires forall w:: w in AVLContentMultiset(newLeft) ==> w <= u
	requires AVLHeight(right) <= AVLHeight(orgLeft)
	requires AVLHeight(orgLeft)-1 <= AVLHeight(newLeft) <= AVLHeight(orgLeft)
	ensures u in AVLContentMultiset(orgLeft)
	ensures forall w:: w in AVLContentMultiset(right) ==> w >= u
	ensures AVLHeight(right)-1 <= AVLHeight(newLeft) <= AVLHeight(right)+1
	ensures ValidSiblings(newLeft,u,right)
	ensures AVLContentMultiset(ConstructAVL(newLeft,u,right)) == AVLContentMultiset(t)-multiset{x}
	ensures u <= x
{}

lemma LemmaDeleteMinFromRight( t: AVLTree, orgRight: AVLTree, newRight: AVLTree, left: AVLTree, u: int, x: int )
	requires IsValidAVL(t)
	requires IsValidAVL(orgRight)
	requires IsValidAVL(newRight)
	requires IsValidAVL(left)
	requires t != EmptyAVL
	requires LeftTree(t) == left
	requires RightTree(t) == orgRight
	requires RootValue(t) == x
	requires AVLContentMultiset(orgRight) == AVLContentMultiset(newRight)+multiset{u}
	requires forall w:: w in AVLContentMultiset(newRight) ==> w >= u
	requires AVLHeight(left) <= AVLHeight(orgRight)
	requires AVLHeight(orgRight)-1 <= AVLHeight(newRight) <= AVLHeight(orgRight)
	ensures u in AVLContentMultiset(orgRight)
	ensures forall w:: w in AVLContentMultiset(left) ==> w <= u
	ensures AVLHeight(left)-1 <= AVLHeight(newRight) <= AVLHeight(left)+1
	ensures ValidSiblings(left,u,newRight)
	ensures AVLContentMultiset(ConstructAVL(left,u,newRight)) == AVLContentMultiset(t)-multiset{x}
	ensures u >= x
{}

method DeleteFromAVL( t: AVLTree, x: int ) returns (res: AVLTree)
	decreases TreeSize(t)
	requires IsValidAVL(t)
	ensures IsValidAVL(res)
	ensures AVLHeight(t)-1 <= AVLHeight(res) <= AVLHeight(t)
	ensures AVLContentMultiset(res) == AVLContentMultiset(t)-multiset{x}
	ensures AVLContentMultiset(res) <= AVLContentMultiset(t)
{
	res := EmptyAVL;
	if t==EmptyAVL
	{
		res := EmptyAVL;
		return;
	}
	assert t != EmptyAVL;
	var y := RootValue(t);
	var left := LeftTree(t);
	var right := RightTree(t);
	if x==y
	{
		if left==EmptyAVL
		{
			HeightLemmas(left);
			HeightLemmas(right);
			HeightLemmas(t);
			res := right;
			return;
		}
		if right==EmptyAVL
		{
			HeightLemmas(left);
			HeightLemmas(right);
			HeightLemmas(t);
			res := left;
			return;
		}
		if AVLHeight(left) >= AVLHeight(right)
		{
			var u := AVLMax(left);
			assert u in AVLContentMultiset(left);
			var newLeft := DeleteFromAVL(left,u);
			SubtractAddNoChange(AVLContentMultiset(left),u);
			calc ==
			{
				AVLContentMultiset(left);
				AVLContentMultiset(left)-multiset{u}+multiset{u};
				AVLContentMultiset(newLeft)+multiset{u};
			}
			assert AVLContentMultiset(left) == AVLContentMultiset(newLeft)+multiset{u};
			SupersetLEImpliesSubsetLE(AVLContentMultiset(newLeft),AVLContentMultiset(left),u);
			LemmaDeleteMaxFromLeft(t,left,newLeft,right,u,x);
			res := ConstructAVL(newLeft,u,right);
			assert AVLHeight(t)-1 <= AVLHeight(res) <= AVLHeight(t);
			assert AVLContentMultiset(res) == AVLContentMultiset(t)-multiset{x};
			SubtractionGivesSubset(AVLContentMultiset(t),AVLContentMultiset(res),multiset{x});
			return;
		}
		var u := AVLMin(right);
		var newRight := DeleteFromAVL(right,u);
		assert AVLContentMultiset(newRight) == AVLContentMultiset(right)-multiset{u};
		LemmaDeleteMinFromRight(t,right,newRight,left,u,x);
		res := ConstructAVL(left,u,newRight);
		assert AVLContentMultiset(res) == AVLContentMultiset(t)-multiset{x};
		SubtractionGivesSubset(AVLContentMultiset(t),AVLContentMultiset(res),multiset{x});
		return;
	}
	if x < y
	{
		ghost var originalLeft := left;
		left := DeleteFromAVL(left,x);
		if AVLHeight(left)-1<=AVLHeight(right)<=AVLHeight(left)+1
		{
			SupersetLEImpliesSubsetLE(AVLContentMultiset(left),AVLContentMultiset(originalLeft),y);
			res := ConstructAVL(left,y,right);
			assert x !in AVLContentMultiset(right);
			assert x !in multiset{y};
			ShiftSubtraction(AVLContentMultiset(originalLeft),multiset{y},x);
			ShiftSubtraction(AVLContentMultiset(originalLeft)+multiset{y},AVLContentMultiset(right),x);
			calc ==
			{
				AVLContentMultiset(t)-multiset{x};
				AVLContentMultiset(ConstructAVL(originalLeft,y,right))-multiset{x};
				AVLContentMultiset(originalLeft)+multiset{y}+AVLContentMultiset(right)-multiset{x};
				(AVLContentMultiset(originalLeft)+multiset{y})+AVLContentMultiset(right)-multiset{x};
				AVLContentMultiset(originalLeft)+multiset{y}-multiset{x}+AVLContentMultiset(right);
				(AVLContentMultiset(originalLeft)+multiset{y})-multiset{x}+AVLContentMultiset(right);
				(AVLContentMultiset(originalLeft)+multiset{y}-multiset{x})+AVLContentMultiset(right);
				(AVLContentMultiset(originalLeft)-multiset{x}+multiset{y})+AVLContentMultiset(right);
				AVLContentMultiset(originalLeft)-multiset{x}+multiset{y}+AVLContentMultiset(right);
				AVLContentMultiset(left)+multiset{y}+AVLContentMultiset(right);
				AVLContentMultiset(res);
			}
			assert AVLContentMultiset(res) == AVLContentMultiset(t)-multiset{x};
			SubtractionGivesSubset(AVLContentMultiset(t),AVLContentMultiset(res),multiset{x});
			assert AVLContentMultiset(res) <= AVLContentMultiset(t);
			return;
		}
		HeightLemmas(left);
		assert AVLHeight(left) >= 0;
		assert AVLHeight(right) == AVLHeight(left)+2 >= 2;
		HeightLemmas(right);
		if AVLHeight(RightTree(right))>=AVLHeight(LeftTree(right))
		{
			//        y                               z
			//       / \                             / \
			// left=A   z          ------>          y   C
			//         / \                         / \
			//        B   C                       A   B
			var A := left;
			var B := LeftTree(right);
			assert right != EmptyAVL;
			var z := RootValue(right);
			var C := RightTree(right);
			DeletionRotateLeft(t,x,originalLeft,right,A,y,B,z,C);
			res := ConstructAVL(ConstructAVL(A,y,B),z,C);
			assert AVLContentMultiset(res) == AVLContentMultiset(t)-multiset{x};
			SubtractionGivesSubset(AVLContentMultiset(t),AVLContentMultiset(res),multiset{x});
			return;
		}
		//        y                                    u
		//       / \                                  / \
		// left=A   z        ------>                 /   \
		//         / \                              y     z
		//        u   D                            / \   / \
		//       / \                              A   B C   D
		//      B   C
		var A := left;
		var leftright := LeftTree(right);
		var B := LeftTree(leftright);
		var C := RightTree(leftright);
		var D := RightTree(right);
		var z := RootValue(right);
		var u := RootValue(leftright);
		DeletionDoubleRotateLeft(t,x,originalLeft,right,leftright,A,y,B,u,C,z,D);
		res := ConstructAVL(ConstructAVL(A,y,B),u,ConstructAVL(C,z,D));
		assert AVLContentMultiset(res) == AVLContentMultiset(t)-multiset{x};
		SubtractionGivesSubset(AVLContentMultiset(t),AVLContentMultiset(res),multiset{x});
		return;
	}
	else
	{
		assert x > y;
		ghost var originalRight := right;
		right := DeleteFromAVL(right,x);
		assert AVLContentMultiset(right) == AVLContentMultiset(originalRight)-multiset{x};
		if AVLHeight(right) >= AVLHeight(left)-1
		{
			res := ConstructAVL(left,y,right);
			assert x !in AVLContentMultiset(left);
			assert x !in multiset{y};
			AssociateSubtraction(multiset{y},AVLContentMultiset(originalRight),x);
			AssociateSubtraction(AVLContentMultiset(left)+multiset{y},AVLContentMultiset(originalRight),x);
			AssociateUnion(AVLContentMultiset(left),multiset{y},AVLContentMultiset(originalRight)-multiset{x});
			calc ==
			{
				AVLContentMultiset(res);
				AVLContentMultiset(ConstructAVL(left,y,right));
				AVLContentMultiset(left)+multiset{y}+AVLContentMultiset(right);
				AVLContentMultiset(left)+multiset{y}+(AVLContentMultiset(originalRight)-multiset{x});
				(AVLContentMultiset(left)+multiset{y})+(AVLContentMultiset(originalRight)-multiset{x});
				AVLContentMultiset(left)+multiset{y}+AVLContentMultiset(originalRight)-multiset{x};
				AVLContentMultiset(t)-multiset{x};
			}
			assert AVLContentMultiset(res) == AVLContentMultiset(t)-multiset{x};
			SubtractionGivesSubset(AVLContentMultiset(t),AVLContentMultiset(res),multiset{x});
			assert AVLContentMultiset(res) <= AVLContentMultiset(t);
			return;
		}
		var rightleft := RightTree(left);
		if AVLHeight(rightleft)<=AVLHeight(LeftTree(left))
		{
			//         y                       z
			//        / \                     / \
			//       z   C=right  ----->     A   y
			//      / \                         / \
			//     A   B                       B   C
			var A := LeftTree(left);
			var B := RightTree(left);
			assert IsValidAVL(right);
			HeightLemmas(right);
			assert AVLHeight(right) >= 0;
			assert AVLHeight(left) == AVLHeight(right)+2 >= 2;
			HeightLemmas(left);
			assert left != EmptyAVL;
			var z := RootValue(left);
			var C := right;
			DeletionRotateRight(t,x,originalRight,left,A,z,B,y,C);
			res := ConstructAVL(A,z,ConstructAVL(B,y,C));
			assert AVLContentMultiset(res) == AVLContentMultiset(t)-multiset{x};
			SubtractionGivesSubset(AVLContentMultiset(t),AVLContentMultiset(res),multiset{x});
			assert AVLContentMultiset(res) <= AVLContentMultiset(t);
			return;
		}
		//         y                                  u
		//        / \                                / \
		//       z   D                              /   \
		//      / \            ---->               z     y
		//     A   u                              / \   / \
		//        / \                            A   B C   D
		//       B   C
		var A := LeftTree(left);
		var z := RootValue(left);
		ghost var leftleft := LeftTree(left);
		assert IsValidAVL(leftleft);
		HeightLemmas(leftleft);
		assert AVLHeight(leftleft) >= 0;
		assert AVLHeight(rightleft) > AVLHeight(leftleft)  >= 0;
		HeightLemmas(rightleft);
		assert rightleft != EmptyAVL;
		var u := RootValue(rightleft);
		var B := LeftTree(rightleft);
		var C := RightTree(rightleft);
		var D := right;
		assert u in AVLContentMultiset(left);
		assert forall w:: w in AVLContentMultiset(left) ==> w <= y;
		assert z <= u <= y;
		assert x > y;
		DeletionDoubleRotateRight(t,x,originalRight,left,rightleft,A,z,B,u,C,y,D);
		res := ConstructAVL(ConstructAVL(A,z,B),u,ConstructAVL(C,y,D));
		assert AVLContentMultiset(res) == AVLContentMultiset(t)-multiset{x};
		SubtractionGivesSubset(AVLContentMultiset(t),AVLContentMultiset(res),multiset{x});
		return;
	}
	assert false;
}

method RecursiveSearchInAVL( t: AVLTree, x: int ) returns (found: bool)
	requires IsAVLSorted(t)
	ensures found <==> x in AVLContentMultiset(t)
{
	if t==EmptyAVL {return false;}
	match t
	case RootedAVL(h,left,z,right) =>
	{
		if x==z { return true; }
		if x<z
		{
			found := RecursiveSearchInAVL(left,x);
			return;
		}
		found := RecursiveSearchInAVL(right,x);
	}	
}

function TreeSize( t: AVLTree ): int
	ensures TreeSize(t)>=0
	ensures TreeSize(t)==|AVLContentSeq(t)|
	ensures TreeSize(t)==|AVLContentMultiset(t)|
{
	match t
	case EmptyAVL => 0
	case RootedAVL(h,left,x,right) => TreeSize(left)+1+TreeSize(right)
}

lemma ShiftSubtraction( A: multiset<int>, B: multiset<int>, x: int )
	requires x !in B
	ensures A-multiset{x}+B == A+B-multiset{x}
{}

lemma AssociateSubtraction( A: multiset<int>, B: multiset<int>, x: int )
	requires x !in A
	ensures A+(B-multiset{x}) == (A+B)-multiset{x}
{}

lemma AssociateUnion( A: multiset<int>, B: multiset<int>, C: multiset<int> )
	ensures A+(B+C) == (A+B)+C
{}

lemma SubtractAddNoChange( A: multiset<int>, x: int )
	requires x in A
	ensures (A-multiset{x})+multiset{x} == A-multiset{x}+multiset{x} == A
{
}

lemma SubtractionGivesSubset( A: multiset<int>, B: multiset<int>, C: multiset<int> )
	requires B == A-C
	ensures B <= A
{}

lemma SupersetLEImpliesSubsetLE( A: multiset<int>, B: multiset<int>, x: int )
	requires A <= B
	requires forall w:: w in B ==> w <= x
	ensures forall w:: w in A ==> w <= x
{}

lemma BothGEImpliesUnionGE( A: multiset<int>, B: multiset<int>, C: multiset<int>, x: int )
	requires C==A+B
	requires forall w:: w in A ==> w >= x
	requires forall w:: w in B ==> w >= x
	ensures forall w:: w in C ==> w >= x
{
}

lemma BothLEImpliesUnionLE( A: multiset<int>, B: multiset<int>, C: multiset<int>, x: int )
	requires C==A+B
	requires forall w:: w in A ==> w <= x
	requires forall w:: w in B ==> w <= x
	ensures forall w:: w in C ==> w <= x
{
}

lemma BothGEImpliesUnionGE1( A: multiset<int>, u: int, C: multiset<int>, x: int )
	requires C==A+multiset{u}
	requires forall w:: w in A ==> w >= x
	requires u >= x
	ensures forall w:: w in C ==> w >= x
{
	BothGEImpliesUnionGE(A,multiset{u},C,x);
}

lemma BothLEImpliesUnionLE1( A: multiset<int>, u: int, C: multiset<int>, x: int )
	requires C==A+multiset{u}
	requires forall w:: w in A ==> w <= x
	requires u <= x
	ensures forall w:: w in C ==> w <= x
{
	BothLEImpliesUnionLE(A,multiset{u},C,x);
}

//         y                      x
//        / \                    / \
//     X=x   C        ----->    A   y                 |A| == |C|+1
//      / \                        / \                |B|+1 >= |A| >= |B|
//     A   B                      B   C
lemma InsertionRotateRight( t: AVLTree, u: int, orgleft: AVLTree, X: AVLTree, A: AVLTree, x: int, B: AVLTree, y: int, C: AVLTree )
	requires x <= y
	requires u < y
	requires IsValidAVL(t)
	requires IsValidAVL(orgleft)
	requires IsValidAVL(X)
	requires IsValidAVL(A)
	requires IsValidAVL(B)
	requires IsValidAVL(C)
	requires AVLHeight(A) == AVLHeight(C)+1
	requires AVLHeight(B) <= AVLHeight(A) <= AVLHeight(B)+1
	requires AVLHeight(C)-1 <= AVLHeight(orgleft) <= AVLHeight(C)+1
	requires t != EmptyAVL
	requires LeftTree(t) == orgleft
	requires RightTree(t) == C
	requires RootValue(t) == y
	requires X != EmptyAVL
	requires LeftTree(X) == A
	requires RightTree(X) == B
	requires RootValue(X) == x
	requires AVLContentMultiset(X) == AVLContentMultiset(orgleft)+multiset{u}

	ensures IsValidAVL(ConstructAVL(A,x,ConstructAVL(B,y,C)))
	ensures AVLContentMultiset(ConstructAVL(A,x,ConstructAVL(B,y,C))) == AVLContentMultiset(t)+multiset{u}
{
	assert AVLHeight(B)-1 <= AVLHeight(C) <= AVLHeight(B)+1;
	assert AVLContentMultiset(B) <= AVLContentMultiset(X);
	BothLEImpliesUnionLE1(AVLContentMultiset(orgleft),u,AVLContentMultiset(X),y);
	assert forall w:: w in AVLContentMultiset(X) ==> w <= y;
	SupersetLEImpliesSubsetLE(AVLContentMultiset(B),AVLContentMultiset(X),y);
	assert IsValidAVL(ConstructAVL(B,y,C));
}

//         y                      x
//        / \                    / \
//     X=x   C        ----->    A   y                 |A| == |C|+1
//      / \                        / \                |B|+1 >= |A| >= |B|
//     A   B                      B   C
lemma DeletionRotateRight( t: AVLTree, u: int, orgright: AVLTree, X: AVLTree, A: AVLTree, x: int, B: AVLTree, y: int, C: AVLTree )
	requires x <= y
	requires u > y
	requires IsValidAVL(t)
	requires IsValidAVL(orgright)
	requires IsValidAVL(X)
	requires IsValidAVL(A)
	requires IsValidAVL(B)
	requires IsValidAVL(C)
	requires AVLHeight(A) == AVLHeight(C)+1
	requires AVLHeight(B) <= AVLHeight(A) <= AVLHeight(B)+1
	requires AVLHeight(C) == AVLHeight(orgright)-1
	requires t != EmptyAVL
	requires RightTree(t) == orgright
	requires LeftTree(t) == X
	requires RootValue(t) == y
	requires X != EmptyAVL
	requires A == LeftTree(X)
	requires x == RootValue(X)
	requires B == RightTree(X)
	requires AVLContentMultiset(C) == AVLContentMultiset(orgright)-multiset{u}

	ensures IsValidAVL(ConstructAVL(A,x,ConstructAVL(B,y,C)))
	ensures AVLContentMultiset(ConstructAVL(A,x,ConstructAVL(B,y,C))) == AVLContentMultiset(t)-multiset{u}
	ensures AVLHeight(t)-1 <= AVLHeight(ConstructAVL(A,x,ConstructAVL(B,y,C))) <= AVLHeight(t)
{
	assert IsValidAVL(ConstructAVL(B,y,C));
	assert IsValidAVL(ConstructAVL(A,x,ConstructAVL(B,y,C)));
	calc ==
	{
		AVLContentMultiset(ConstructAVL(A,x,ConstructAVL(B,y,C)));
		AVLContentMultiset(A)+multiset{x}+AVLContentMultiset(B)+multiset{y}+AVLContentMultiset(C);
		AVLContentMultiset(A)+multiset{x}+AVLContentMultiset(B)+multiset{y}+(AVLContentMultiset(orgright)-multiset{u});
		AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,orgright))-multiset{u};
		AVLContentMultiset(t)-multiset{u};
	}
}

//      x                           y
//     / \                         / \
//    A   y=Y         ----->      x   C               |C| == |A|+1
//       / \                     / \                  |B|+1 >= |C| >= |B|
//      B   C                   A   B
lemma InsertionRotateLeft( t: AVLTree, u: int, orgright: AVLTree, Y: AVLTree, A: AVLTree, x: int, B: AVLTree, y: int, C: AVLTree )
	requires x <= y
	requires u > x
	requires IsValidAVL(t)
	requires IsValidAVL(orgright)
	requires IsValidAVL(Y)
	requires IsValidAVL(A)
	requires IsValidAVL(B)
	requires IsValidAVL(C)
	requires AVLHeight(C) == AVLHeight(A)+1
	requires AVLHeight(B) <= AVLHeight(C) <= AVLHeight(B)+1
	requires AVLHeight(A)-1 <= AVLHeight(orgright) <= AVLHeight(A)+1
	requires t != EmptyAVL
	requires LeftTree(t) == A
	requires RightTree(t) == orgright
	requires RootValue(t) == x
	requires Y != EmptyAVL
	requires LeftTree(Y) == B
	requires RightTree(Y) == C
	requires RootValue(Y) == y
	requires AVLContentMultiset(Y) == AVLContentMultiset(orgright)+multiset{u}
	requires AVLHeight(Y) <= AVLHeight(orgright)+1

	ensures IsValidAVL(ConstructAVL(ConstructAVL(A,x,B),y,C))
	ensures AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,C)) == AVLContentMultiset(t)+multiset{u}
	ensures AVLHeight(ConstructAVL(ConstructAVL(A,x,B),y,C)) <= AVLHeight(t)+1
{
	assert IsValidAVL(ConstructAVL(A,x,B));
	assert IsValidAVL(ConstructAVL(ConstructAVL(A,x,B),y,C));
	calc ==
	{
		AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,C));
		AVLContentMultiset(A)+multiset{x}+AVLContentMultiset(B)+multiset{y}+AVLContentMultiset(C);
		AVLContentMultiset(t)+multiset{u};
	}
	assert AVLHeight(ConstructAVL(ConstructAVL(A,x,B),y,C)) <= AVLHeight(t)+1;
}

//      x                           y
//     / \                         / \
//    A   y=Y         ----->      x   C               |C| == |A|+1
//       / \                     / \                  |B|+1 >= |C| >= |B|
//      B   C                   A   B
lemma DeletionRotateLeft( t: AVLTree, u: int, orgleft: AVLTree, Y: AVLTree, A: AVLTree, x: int, B: AVLTree, y: int, C: AVLTree )
	requires x <= y
	requires u < x
	requires IsValidAVL(t)
	requires IsValidAVL(orgleft)
	requires IsValidAVL(Y)
	requires IsValidAVL(A)
	requires IsValidAVL(B)
	requires IsValidAVL(C)
	requires orgleft == LeftTree(t)
	requires t != EmptyAVL
	requires x == RootValue(t)
	requires Y == RightTree(t)
	requires Y != EmptyAVL
	requires y == RootValue(Y)
	requires B == LeftTree(Y)
	requires C == RightTree(Y)
	requires AVLHeight(C) == AVLHeight(A)+1
	requires AVLHeight(B) <= AVLHeight(C) <= AVLHeight(B)+1
	requires AVLHeight(orgleft) == 1+AVLHeight(A)
	requires AVLContentMultiset(A) == AVLContentMultiset(orgleft)-multiset{u}

	ensures IsValidAVL(ConstructAVL(ConstructAVL(A,x,B),y,C))
	ensures AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,C)) == AVLContentMultiset(t)-multiset{u}
{
	assert IsValidAVL(ConstructAVL(A,x,B));
	calc ==
	{
		AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,C));
		AVLContentMultiset(A)+multiset{x}+AVLContentMultiset(B)+multiset{y}+AVLContentMultiset(C);
		AVLContentMultiset(orgleft)-multiset{u}+multiset{x}+AVLContentMultiset(B)+multiset{y}+AVLContentMultiset(C);
		AVLContentMultiset(t)-multiset{u};
	}
}

//         z                      y
//        / \                    / \
//     X=x   D        ----->    /   \                 |X| == |D|+2
//      / \                    x     z                |Y| == |A|+1
//     A   y=Y                / \   / \         
//        / \                A   B C   D
//       B   C
lemma InsertionDoubleRotateRight( t: AVLTree, u: int, orgleft: AVLTree, X: AVLTree, Y: AVLTree, A: AVLTree, x: int, B: AVLTree, y: int, C: AVLTree, z: int, D: AVLTree )
	requires AVLHeight(X) <= AVLHeight(orgleft)+1
	requires AVLHeight(Y) == AVLHeight(A)+1
	requires AVLHeight(D) == AVLHeight(X)-2
	requires x <= y <= z
	requires u < z
	requires IsValidAVL(t)
	requires IsValidAVL(orgleft)
	requires IsValidAVL(X)
	requires IsValidAVL(Y)
	requires IsValidAVL(A)
	requires IsValidAVL(B)
	requires IsValidAVL(C)
	requires IsValidAVL(D)
	requires AVLContentMultiset(X) == AVLContentMultiset(orgleft)+multiset{u}
	requires B == LeftTree(Y)
	requires C == RightTree(Y)
	requires Y != EmptyAVL
	requires y == RootValue(Y)
	requires A == LeftTree(X)
	requires Y == RightTree(X)
	requires x == RootValue(X)
	requires orgleft == LeftTree(t)
	requires D == RightTree(t)
	requires t != EmptyAVL
	requires RootValue(t) == z
	ensures IsValidAVL(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D)))
	ensures AVLHeight(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) <= AVLHeight(t)+1
	ensures AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) == AVLContentMultiset(t)+multiset{u}
{
	assert IsValidAVL(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D)));
	assert AVLHeight(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) <= AVLHeight(t)+1;
	assert AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) == AVLContentMultiset(t)+multiset{u};
}

//         z                      y
//        / \                    / \
//     X=x   D        ----->    /   \                 |X| == |D|+2
//      / \                    x     z                |Y| == |A|+1
//     A   y=Y                / \   / \         
//        / \                A   B C   D
//       B   C
lemma DeletionDoubleRotateRight( t: AVLTree, u: int, orgright: AVLTree, X: AVLTree, Y: AVLTree, A: AVLTree, x: int, B: AVLTree, y: int, C: AVLTree, z: int, D: AVLTree )
	requires AVLHeight(X) == AVLHeight(orgright)+1
	requires AVLHeight(Y) == AVLHeight(A)+1
	requires AVLHeight(X) == AVLHeight(D)+2
	requires x <= y <= z
	requires u > z
	requires IsValidAVL(t)
	requires IsValidAVL(orgright)
	requires IsValidAVL(X)
	requires IsValidAVL(Y)
	requires IsValidAVL(A)
	requires IsValidAVL(B)
	requires IsValidAVL(C)
	requires IsValidAVL(D)
	requires AVLContentMultiset(D) == AVLContentMultiset(orgright)-multiset{u}
	requires B == LeftTree(Y)
	requires C == RightTree(Y)
	requires Y != EmptyAVL
	requires y == RootValue(Y)
	requires A == LeftTree(X)
	requires Y == RightTree(X)
	requires x == RootValue(X)
	requires orgright == RightTree(t)
	requires X == LeftTree(t)
	requires t != EmptyAVL
	requires RootValue(t) == z
	ensures IsValidAVL(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D)))
	ensures AVLHeight(t)-1 <= AVLHeight(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) <= AVLHeight(t)
	ensures AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) == AVLContentMultiset(t)-multiset{u}
{
	assert IsValidAVL(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D)));
	assert AVLHeight(t)-1 <= AVLHeight(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) <= AVLHeight(t);
	assert AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) == AVLContentMultiset(t)-multiset{u};
}

//     x                          y
//    / \                        / \
//   A   z=Z     ----->         /   \                |Z| == |A|+2
//      / \                    x     z               |Y| == |D|+1
//   Y=y   D                  / \   / \
//    / \                    A   B C   D
//   B   C
lemma InsertionDoubleRotateLeft( t: AVLTree, u: int, orgright: AVLTree, Z: AVLTree, Y: AVLTree, A: AVLTree, x: int, B: AVLTree, y: int, C: AVLTree, z: int, D: AVLTree )
	requires AVLHeight(Z) <= AVLHeight(orgright)+1
	requires AVLHeight(Y) == AVLHeight(D)+1
	requires AVLHeight(A) == AVLHeight(Z)-2
	requires x <= y <= z
	requires u > x
	requires IsValidAVL(t)
	requires IsValidAVL(orgright)
	requires IsValidAVL(Z)
	requires IsValidAVL(Y)
	requires IsValidAVL(A)
	requires IsValidAVL(B)
	requires IsValidAVL(C)
	requires IsValidAVL(D)
	requires AVLContentMultiset(Z) == AVLContentMultiset(orgright)+multiset{u}

	requires B == LeftTree(Y)
	requires C == RightTree(Y)
	requires Y != EmptyAVL
	requires y == RootValue(Y)
	requires Y == LeftTree(Z)
	requires D == RightTree(Z)
	requires z == RootValue(Z)
	requires orgright == RightTree(t)
	requires A == LeftTree(t)
	requires t != EmptyAVL
	requires RootValue(t) == x

	ensures IsValidAVL(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D)))
	ensures AVLHeight(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) <= AVLHeight(t)+1
	ensures AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) == AVLContentMultiset(t)+multiset{u}
{
	assert IsValidAVL(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D)));
	assert AVLHeight(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) <= AVLHeight(t)+1;
	assert AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) == AVLContentMultiset(t)+multiset{u};
}

//     x                          y
//    / \                        / \
//   A   z=Z     ----->         /   \                |Z| == |A|+2
//      / \                    x     z               |Y| == |D|+1
//   Y=y   D                  / \   / \
//    / \                    A   B C   D
//   B   C
lemma DeletionDoubleRotateLeft( t: AVLTree, u: int, orgleft: AVLTree, Z: AVLTree, Y: AVLTree, A: AVLTree, x: int, B: AVLTree, y: int, C: AVLTree, z: int, D: AVLTree )
	requires AVLHeight(Z) == AVLHeight(orgleft)+1
	requires AVLHeight(Y) == AVLHeight(D)+1
	requires AVLHeight(Z) == AVLHeight(A)+2
	requires x <= y <= z
	requires u < x
	requires IsValidAVL(t)
	requires IsValidAVL(orgleft)
	requires IsValidAVL(Z)
	requires IsValidAVL(Y)
	requires IsValidAVL(A)
	requires IsValidAVL(B)
	requires IsValidAVL(C)
	requires IsValidAVL(D)
	requires AVLContentMultiset(A) == AVLContentMultiset(orgleft)-multiset{u}

	requires B == LeftTree(Y)
	requires C == RightTree(Y)
	requires Y != EmptyAVL
	requires y == RootValue(Y)
	requires Y == LeftTree(Z)
	requires D == RightTree(Z)
	requires z == RootValue(Z)
	requires orgleft == LeftTree(t)
	requires Z == RightTree(t)
	requires t != EmptyAVL
	requires RootValue(t) == x

	ensures IsValidAVL(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D)))
	ensures AVLHeight(t)-1 <= AVLHeight(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) <= AVLHeight(t)
	ensures AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) == AVLContentMultiset(t)-multiset{u}
{
	assert IsValidAVL(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D)));
	assert AVLHeight(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) <= AVLHeight(t)+1;
	assert AVLContentMultiset(ConstructAVL(ConstructAVL(A,x,B),y,ConstructAVL(C,z,D))) == AVLContentMultiset(t)-multiset{u};
}

/*
method Main()
{
	var a := new int[10];
	print "Hello world\n";
	a[0] := 20;
	a[1] := 0;
	a[2] := 19;
	a[3] := 1;
	a[4] := 18;
	a[5] := 2;
	a[6] := 17;
	a[7] := 3;
	a[8] := 16;
	a[9] := 4;
	AVLSort(a,0,10);
	print a[0], " ";
	print a[1], " ";
	print a[2], " ";
	print a[3], " ";
	print a[4], " ";
	print a[5], " ";
	print a[6], " ";
	print a[7], " ";
	print a[8], " ";
	print a[9], "\n";
}

lemma SortingStep( orga: seq<int>, a0: seq<int>, a1: seq<int>, i: int, j: int, k: int, m0: multiset<int>, m1: multiset<int>, x: int )
	requires 0 <= i <= k < j <= |orga|==|a0|==|a1|
	requires multiset(a0[i..k])+m0 == multiset(orga[i..j])
	requires orga[..i] == a0[..i]
	requires orga[j..] == a0[j..]
	requires a0[..k] == a1[..k]
	requires a0[k+1..] == a1[k+1..]
	requires a1[k] == x
	requires forall u,v:: i<=u<v<k ==> a0[u] <= a0[v]
	requires forall u:: i<=u<k ==> a0[u] <= x
	requires forall w:: w in m0 ==> w >= x
	requires x in m0
	requires m1 == m0-multiset{x}
	ensures orga[..i] == a1[..i]
	ensures orga[j..] == a1[j..]
	ensures forall u,v:: i<=u<v<k+1 ==> a1[u] <= a1[v]
	ensures forall u,w:: i<=u<k+1 && w in m1 ==> a1[u] <= w
	ensures multiset(a1[i..k+1])+m1 == multiset(orga[i..j])
{
	calc ==
	{
		multiset(a1[i..k+1])+m1;
		calc ==
		{
			a1[i..k+1];
			a1[i..k]+[a1[k]];
		}
		multiset(a1[i..k]+[a1[k]])+m1;
		multiset(a1[i..k]+[a1[k]])+(m0-multiset{x});
		multiset(a1[i..k])+multiset([a1[k]])+(m0-multiset{x});
		multiset(a1[i..k])+multiset([x])+(m0-multiset{x});
		multiset(a1[i..k])+multiset{x}+(m0-multiset{x});
		multiset(a1[i..k])+multiset{x}+m0-multiset{x};
		multiset(a0[i..k])+multiset{x}+m0-multiset{x};
		multiset(a0[i..k])+m0+multiset{x}-multiset{x};
		multiset(a0[i..k])+m0;
		multiset(orga[i..j]);
	}
}

method AVLSort( a: array<int>, i: int, j: int )
	requires 0 <= i <= j <= a.Length
	modifies a
	ensures multiset(a[i..j]) == old(multiset(a[i..j]))
	ensures a[..i] == old(a[..i])
	ensures a[j..] == old(a[j..])
	ensures forall u,v:: i<=u<v<j ==> a[u]<=a[v]
{
	var t: AVLTree;
	t := EmptyAVL;
	var k := i;
	ghost var org := a[..];
	while k!=j
		decreases j-k
		invariant i<=k<=j
		invariant multiset(a[i..k]) == AVLContentMultiset(t)
		invariant TreeSize(t) == k-i
		invariant a[..] == org[..]
		invariant IsValidAVL(t)
	{
		t := InsertIntoAVL(t,a[k]);
		k := k+1;
	}
	k := i;
	while k!=j
		decreases j-k
		invariant i<=k<=j
		invariant IsValidAVL(t)
		invariant TreeSize(t) == j-k
		invariant multiset(org[i..j]) == multiset(a[i..k])+AVLContentMultiset(t)
		invariant forall u,v:: i<=u<v<k ==> a[u] <= a[v]
		invariant forall u,v:: i<=u<k && v in AVLContentMultiset(t) ==> a[u] <= v
		invariant a[..i] == org[..i]
		invariant a[j..] == org[j..]
	{
		ghost var a0 := a[..];
		ghost var m0 := AVLContentMultiset(t);
		var x := AVLMin(t);
		a[k] := x;
		t := DeleteFromAVL(t,x);
		k := k+1;
		assert a[k-1] == x;
		ghost var a1 := a[..];
		ghost var m1 := AVLContentMultiset(t);
		SortingStep(org,a0,a1,i,j,k-1,m0,m1,x);
	}
}
*/

