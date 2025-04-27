method Partition( m: multiset<int> )
        returns( pre: multiset<int>, p: int, post: multiset<int> )
    requires |m| > 0
    ensures p in m
    ensures m == pre+multiset{p}+post
    ensures forall z | z in pre :: z <= p
    ensures forall z | z in post :: z >= p
{
    var recursive :| recursive in {true,false};

    if( recursive )
    {
        // Recursive solution
        var x :| x in m;
        var m' := m-multiset{x};
        if m' == multiset{} { return multiset{}, x, multiset{}; }
        pre, p, post := Partition(m');
        if x < p { pre  := pre+multiset{x};  }
        else     { post := post+multiset{x}; }
    }
    else
    {
        // Loop solution
        p :| p in m;
        var m' := m-multiset{p};
        pre := multiset{};
        post := multiset{};
        while m' != multiset{}
            decreases m'
            invariant m == pre+m'+post+multiset{p}
            invariant forall z | z in pre :: z <= p
            invariant forall z | z in post :: z >= p
        {
            var z :| z in m';
            m' := m'-multiset{z};
            if z <= p { pre := pre+multiset{z};   }
            else      { post := post+multiset{z}; }
        }
    }
}

method QuickSelect( m: multiset<int>, k: int )
        returns( pre: multiset<int>, kth: int, post: multiset<int> )
    requires 0 <= k < |m|
    ensures kth in m
    ensures m == pre+multiset{kth}+post
    ensures |pre| == k
    ensures forall z | z in pre :: z <= kth
    ensures forall z | z in post :: z >= kth
{
    var recursive :| recursive in {true,false};

    if recursive
    {
        // Recursive solution
        var p: int;
        pre, p, post := Partition(m);

        // <---------sorted m--------->
        //
        // |    pre    |p|    post    |
        //  ^           ^              ^
        //  0         |pre|           |m|
        //
        //      k?     k?      k?

        if |pre| == k
        {
            return pre, p, post;
        }
        else if k < |pre|
        {
            var post' := post;
            pre, kth, post := QuickSelect(pre,k);
            post := multiset{p}+post+post';
        }
        else
        {
            var pre' := pre;
            pre, kth, post := QuickSelect(post,k-1-|pre'|);
            pre := pre'+pre+multiset{p};
        }
    }
    else
    {
        // Loop solution
        var mid := m;
        pre, post := multiset{}, multiset{};
        while true
            decreases mid
            invariant pre+mid+post == m
            invariant |pre| <= k < |pre|+|mid|
            invariant forall z,w | z in pre && w in mid :: z <= w
            invariant forall z,w | z in post && w in mid :: z >= w

            // <-------------sorted m--------------->
            //
            // |    pre    |    mid    |    post    |
            //  ^           ^    ^      ^            ^
            //  0           i    k      j           |m|
            //
            //  where i == |pre|,  j == |pre+mid|

        {
            var pre', p, post' := Partition(mid);

            // <--------------------sorted m----------------------->
            //
            //            <------------mid------------>
            //
            // |   pre    |    pre'    |p|   post'    |    post    |
            //  ^          ^            ^              ^            ^
            //  0          i            r              j           |m|
            //
            //                   k?     k?     k?
            //
            //  where r == |pre+pre'|

            if k == |pre+pre'|
            {
                return pre+pre', p, post'+post;
            }
            else if |pre+pre'| < k
            {
                mid := post';
                pre := pre+pre'+multiset{p};
            }
            else
            {
                mid := pre';
                post := multiset{p}+post'+post;
            }
        }
    }
}