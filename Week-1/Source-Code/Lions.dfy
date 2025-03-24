// Author: Snorri Agnarsson, snorri@hi.is
// Permalink: https://tinyurl.com/4bn8srk5

lemma Lions1<T>( F: (T)->bool, D: (T,T)->bool, L: (T)->bool, S: (T)->bool, j: (T)->T, Svali: T )
    requires forall x,y: T ::
        (!S(y) || !D(x,y) || F(x)) &&
        (S(Svali)) &&
        (!S(y) || L(j(y))) &&
        (!S(y) || D(j(y),y)) &&
        (!L(x) || !F(x))
    ensures false
{}

lemma Lions2<T>( F: (T)->bool, D: (T,T)->bool, L: (T)->bool, S: (T)->bool, j: (T)->T, Svali: T )
    requires forall x,y: T ::
        (!S(y) || !D(x,y) || F(x)) &&
        (S(Svali)) &&
        (!S(y) || L(j(y))) &&
        (!S(y) || D(j(y),y))
    ensures L(j(Svali)) && F(j(Svali))
{}

lemma Lions3<T>( F: (T)->bool, D: (T,T)->bool, L: (T)->bool, S: (T)->bool, j: (T)->T, Svali: T )
    requires forall x,y: T ::
        (!S(y) || !D(x,y) || F(x)) &&
        (S(Svali)) &&
        (!S(y) || L(j(y))) &&
        (!S(y) || D(j(y),y))
    ensures exists x: T :: L(x) && F(x)
{}

lemma Lions4<T>( F: (T)->bool, D: (T,T)->bool, L: (T)->bool, S: (T)->bool, Svali: T )
    requires forall x,y: T :: (S(y) && D(x,y)) ==> F(x)
    requires S(Svali)
    requires forall y: T :: S(y) ==> (exists x: T :: L(x) && D(x,y))
    requires !exists x: T :: L(x) && F(x)
    ensures false
{}

lemma Lions5<T>( F: (T)->bool, D: (T,T)->bool, L: (T)->bool, S: (T)->bool, Svali: T )
    requires forall x,y: T :: (S(y) && D(x,y)) ==> F(x)
    requires S(Svali)
    requires forall y: T :: S(y) ==> (exists x: T :: L(x) && D(x,y))
    ensures exists x: T :: L(x) && F(x)
{}

lemma Lions6<T>( F: (T)->bool, D: (T,T)->bool, L: (T)->bool, S: (T)->bool )
    requires forall x,y: T :: (S(y) && D(x,y)) ==> F(x)
    requires exists y: T :: S(y)
    requires forall y: T :: S(y) ==> (exists x: T :: L(x) && D(x,y))
    ensures exists x: T :: L(x) && F(x)
{}

lemma Lions7<T>( IsPeaceful: (T)->bool, Drinks: (T,T)->bool, IsLion: (T)->bool, IsFruitdrink: (T)->bool )
    requires forall x,y: T :: (IsFruitdrink(y) && Drinks(x,y)) ==> IsPeaceful(x)
    requires exists y: T :: IsFruitdrink(y)
    requires forall y: T :: IsFruitdrink(y) ==> (exists x: T :: IsLion(x) && Drinks(x,y))
    ensures exists x: T :: IsLion(x) && IsPeaceful(x)
{}

lemma Lions8<Animals,Beverages> ( IsPeaceful: (Animals)->bool
                                , Drinks: (Animals,Beverages)->bool
                                , IsLion: (Animals)->bool
                                , IsFruitdrink: (Beverages)->bool 
                                )
    requires forall x: Animals, y: Beverages :: (IsFruitdrink(y) && Drinks(x,y)) ==> IsPeaceful(x)
    requires exists y: Beverages :: IsFruitdrink(y)
    requires forall y: Beverages :: IsFruitdrink(y) ==> (exists x: Animals :: IsLion(x) && Drinks(x,y))
    ensures exists x: Animals :: IsLion(x) && IsPeaceful(x)
{}

lemma Lions9<Animals,Beverages> ( IsPeaceful: (Animals)->bool
                                , Drinks: (Animals,Beverages)->bool
                                , IsLion: (Animals)->bool
                                , IsFruitdrink: (Beverages)->bool 
                                )
    requires forall x: Animals, y: Beverages :: (IsFruitdrink(y) && Drinks(x,y)) ==> IsPeaceful(x)
    requires exists y: Beverages :: IsFruitdrink(y)
    requires forall y: Beverages :: IsFruitdrink(y) ==> (exists x: Animals :: IsLion(x) && Drinks(x,y))
{
    assert exists x: Animals :: IsLion(x) && IsPeaceful(x);
}

lemma LionsA<Animals,Beverages> ( IsPeaceful: (Animals)->bool
                                , Drinks: (Animals,Beverages)->bool
                                , IsLion: (Animals)->bool
                                , IsFruitdrink: (Beverages)->bool 
                                )
                                returns( r: Animals )
    requires forall x: Animals, y: Beverages :: (IsFruitdrink(y) && Drinks(x,y)) ==> IsPeaceful(x)
    requires exists y: Beverages :: IsFruitdrink(y)
    requires forall y: Beverages :: IsFruitdrink(y) ==> (exists x: Animals :: IsLion(x) && Drinks(x,y))
    ensures IsLion(r) && IsPeaceful(r)
{
    r :| IsLion(r) && IsPeaceful(r);
}

lemma LionsB<T>( F: (T)->bool, D: (T,T)->bool, L: (T)->bool, S: (T)->bool, j: (T)->T, Svali: T )
    requires forall x,y: T ::
        (!S(y) || !D(x,y) || F(x)) &&
        (S(Svali)) &&
        (!S(y) || L(j(y))) &&
        (!S(y) || D(j(y),y)) &&
        (!L(x) || !F(x))
{
    assert false;
}

lemma LionsC<T>( F: (T)->bool, D: (T,T)->bool, L: (T)->bool, S: (T)->bool, j: (T)->T, Svali: T )
    requires forall x,y: T :: !S(y) || !D(x,y) || F(x)
    requires S(Svali)
    requires forall y: T :: !S(y) || L(j(y))
    requires forall y: T :: !S(y) || D(j(y),y)
    requires forall x: T :: !L(x) || !F(x)
{
    assert false;
}