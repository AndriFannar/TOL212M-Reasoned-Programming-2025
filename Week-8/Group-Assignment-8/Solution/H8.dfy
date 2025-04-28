method Partition( m: multiset<int> )
        returns( pre: multiset<int>, p: int, post: multiset<int> )
    requires |m| > 0
    ensures p in m
    ensures m == pre+multiset{p}+post
    ensures forall z | z in pre :: z <= p
    ensures forall z | z in post :: z >= p
{
    /*
    // Loop solution:
    p :| p in m;
    var m' := m-multiset{p};
    pre := multiset{};
    post := multiset{};
    while m' != multiset{}
        decreases m'
        invariant p in m
        invariant m == m'+pre+multiset{p}+post
        invariant forall z | z in pre :: z <= p
        invariant forall z | z in post :: z >= p
    {
        var x :| x in m';
        m' := m'-multiset{x};
        if x < p { pre  := pre+multiset{x};  }
        else     { post := post+multiset{x}; }
    }
    */
    // Recursive solution:
    var x :| x in m;
    var m' := m-multiset{x};
    if m' == multiset{} { return multiset{}, x, multiset{}; }
    pre, p, post := Partition(m');
    if x < p { pre  := pre+multiset{x};  }
    else     { post := post+multiset{x}; }
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
    // Loop solution:
    var mid := m;
    pre, post := multiset{}, multiset{};
    while true
        decreases mid
        invariant pre+mid+post == m
        invariant |pre| <= k < |pre|+|mid|
        invariant forall z,w | z in pre && w in mid :: z <= w
        invariant forall z,w | z in post && w in mid :: z >= w
    {
        var pre', p, post' := Partition(mid);
        if |pre+pre'| == k { return pre+pre', p, post'+post; }
        if |pre+pre'| < k
        {
            pre := pre+pre'+multiset{p};
            mid := post';
        }
        else
        {
            mid := pre';
            post := multiset{p}+post'+post;
        }
    }

    /*
    // Recursive solution
    var p;
    pre, p, post := Partition(m);
    if |pre| == k { return pre, p, post; }
    if |pre| > k
    {
        var post';
        pre, kth, post' := QuickSelect(pre,k);
        post := post'+multiset{p}+post;
    }
    else
    {
        var pre';
        pre', kth, post := QuickSelect(post,k-|pre|-1);
        pre := pre+multiset{p}+pre';
    }
    */
}