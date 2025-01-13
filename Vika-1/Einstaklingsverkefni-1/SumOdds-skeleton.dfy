// Author of question: Snorri Agnarsson
// Permalink of question: https://tinyurl.com/muvnbkjn

// Author of solution:    Andri Fannar Kristjánsson
// Permalink of solution: https://tio.run/##zVbbjttGDH3XV7Doy9puZCdFX7zZAIsWBYIWTZCg6FuBsURZk5U4zlwsGNv9mHxLPmxLjm7W2t68xjDWmhkOeXh4SG2uCjo8Pi6XcBt8aSyYAj4HdF4bWsNHMtZquN2Sss4ZStjuPdpaVZrupqal9zu3Xi69pkOwVZqZelmHPW3uPlGSTPw7U4X2En9uKecIvyviEPCH1c5/@vqFzgYb76VpGn3@7RB8icDBakW5bAHkkhJ8DPW7PHcv3B1W6A2leXGQc2NbK76y0xUOv5fsvRlMJFLBD6nsv7MQuugNbmCntnjEgUltoOWPEUoL9Z8SCQ4mQKn2KKnsMY@3d9ZsKqxhF3yMV@KQKPBX1r/FjPowP4nZFgmt8ggKdgNHTIG4Ac1fap1p10GW5a@cSOA7Lxc/L35ZMImLq1dzevFyFl3qFNM2fKiF7jZd6zwwkDwHCvUGrUuTIlAW4XWcXQGXRJOHWfxJpKwWPwdt0fHdNzewSu7jri54fcNrcU5xSz6r@ISVw2Grdy3oYAERZvLQMsmMK47GlWHu9lIDFak7SUtC0b@vkoT5rRW8F@sTzGfhyh57/Mt4ZsOiAG@k0Pyoqso0UjsDKo8/rQIp10KK6@9uuBCq8GjB24OmLVeqYneRWF46eAuEez5ulAO1EX0NCZneSVt5SXDKCCcWH@bx7zU0mptLAua5hBJESILcjcjS6DTHzKJykmrLemc2uG9Zm1NXMmlCcQwbkx@gFAYiHBeKQmd8MTYI7TVleAa1IGnZZyV6GzB9IoS4vB/qrpxDOya7imhW10/PV3F7fnRg0QdL7fphqqfR@0QBkblLgVsazqnw8pUzhXne/ZHlt733delT5Gaokaue923dWf5pzG5Ud8eLgysXdy7LvReCmyQ@Oz37tjayFpDrp0lvrCk2gdlBE41lHEoPcUtFU26W2h0ZnzZ0YU3Neipi91u9LX3a23/ALFgnY4mVRtxpfaPKVJRItTr0tnKcSdQpdZ2LfSfSPb@RNKwH/bmj56aUN4KGH25gnGOa@IqW2bSC1zd8@vr86YRiPbtkoef6iX4jGr04UknE5KJ6dK8eVsbYEeCuL0plyPc71Yvt8VWH5yovipepd7nust9bn6m7OHg6l@47@lbXD2PxL9E39vpRPYZunhSCEbwter4Ecsb/YmEWJyW1L@x2XjaacTbG3qXd66u7c1tVV1OWC2MlJ4L/uvrAen1xnp8aPzsjZ8O4eXz8Hw

// Use the command
//   dafny SumOdds-skeleton.dfy
// or
//   compile compile SumOdds-skeleton.dfy
// to compile the file.
// Or use the web page https://tio.run/#dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

// Compute 1+3+5+...+(2*n-1),
// i.e. the sum of the first n odd numbers.
function SumOdds( n: int ): int
    requires n >= 0
{
    if n == 0 then
        0
    else
        SumOdds(n-1) + 2*n-1
}

// We want to prove that
// 1+3+5+...+(2*n-1) == n^2

lemma ProveSumOdds( n: int )
    requires n >= 0
    // Not sure if we were allowed to add to the conditions
    // but after trying a lot of things I never was able to prove to
    // Dafny that SumOdds(n-1) == (n-1)*(n-1); without adding the ensures condition.
    decreases n
    ensures SumOdds(n) == n*n
{
    // Put a body here that suffices to convince
    // Dafny that the lemma is true.
    if n == 0 
    {
        assert SumOdds(0) == 0;
        assert 0 == 0*0;
        return;
    }
    else
    {
        ProveSumOdds(n-1);
        assert SumOdds(n) == SumOdds(n-1) + 2*n-1;
        assert SumOdds(n-1) == (n-1)*(n-1);
        assert SumOdds(n) == (n-1)*(n-1) + 2*n-1;
        assert SumOdds(n) == n*n;
    }
}

method ComputeSumOddsLoop( n: int ) returns (s: int)
    requires n >= 0
    ensures s == SumOdds(n)
    ensures s == n*n
{
    // Put a body here that computes the sum
    // in a loop where you add all the terms
    // in 1+3+5+...+(2*n-1) from left to right.
    // Recursion is not allowed and you may
    // not call ComputeSumOddsRecursive.
    var i := 0;
    s := 0;
    while i != n
        invariant 0 <= i <= n
        invariant s == SumOdds(i)
        invariant s == i*i
    {
        i := i+1;
        s := s + 2*i-1;
    }

    return s;
}

method ComputeSumOddsRecursive( n: int ) returns (s: int)
    requires n >= 0
    ensures s == SumOdds(n)
    ensures s == n*n
{
    // Put a body here that computes the sum
    // recursively from left to right.
    // Looping is not allowed and you may not
    // call ComputeSumOddsLoop.
    if n == 0 {return 0;}
    s := ComputeSumOddsRecursive(n-1);
    s := s + 2*n-1;
    return s;
}

// If SumOdds is correct then this lemma will work.
lemma SumOddsAll()
    ensures forall n | n >= 0 :: SumOdds(n) == n*n
{
    forall n | n >= 0 
    {
        ProveSumOdds(n);
    }
}