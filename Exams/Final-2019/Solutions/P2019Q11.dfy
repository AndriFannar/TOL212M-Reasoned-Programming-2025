method Mul ( x: int, y: int ) returns ( p: int )
    decreases y
    requires x >= 0 && y >= 0
    ensures p == x*y
{
    if y == 0 { return 0; }
    p := Mul(x+x,y/2);
    if y%2 == 1
    {
        p := p+x;
    }
    else
    {
        assert (y/2)*2 == y;
    }
}