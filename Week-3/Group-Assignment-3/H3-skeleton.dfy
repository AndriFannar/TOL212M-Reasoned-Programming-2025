// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is

// Höfundur lausnar:     Andri Fannar Kristjánsson, afk6@hi.is
// Permalink lausnar:    https://shorturl.at/fKfzr

// Insertion sort með hjálp helmingunarleitar.
// Insertion sort with the help of binary search.

method Search( s: seq<int>, x: int ) returns ( k: int )
  // Ekki má breyta forskilyrðum eða eftirskilyrðum fallsins
  // Do not change the preconditions or the postconditions
  decreases |s|
  requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
  ensures 0 <= k <= |s|
  ensures forall i | 0 <= i < k :: s[i] <= x
  ensures forall i | k <= i < |s| :: s[i] >= x
  ensures forall z | z in s[..k] :: z <= x
  ensures forall z | z in s[k..] :: z >= x
  ensures s == s[..k]+s[k..]

  // S: | <= x | >= x |
  //     ^      ^      ^
  //     0      k     |s|
{
  // Base case, return 0 if s is empty.
  if s == [] { k := 0; return; }

  // Caclulate center index.
  var i := |s|/2;

  // Split based on value of s[i].
  if s[i] <= x
  {
    k := Search(s[i+1..], x);
    k := k + (i+1);
  }
  else
  {
    k := Search(s[..i], x);
  }
  return;
}

method Sort( m: multiset<int> ) returns ( r: seq<int> )
  ensures multiset(r) == m
  ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
{
  // Setjið viðeigandi frumstillingu á r og rest hér.
  // r er skilabreyta en rest er ný breyta sem þið búið til.
  // Put appropriate initializations of r and rest here.
  // r is the return variable but rest is a new variable you should create.
  r := [];
  var rest := m;
  while rest != multiset{}
    // Ekki breyta fastayrðingu lykkjunnar
    // Do not change the loop invariant
    decreases rest
    invariant m == multiset(r)+rest
    invariant forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
  {
    // Setjið viðeigandi stofn lykkjunnar hér.
    // Fjarlægið eitt gildi úr rest með
    //    var x :| x in rest;
    //    rest := rest-multiset{x};
    // og notið Search til að finna réttan stað
    // í r til að stinga [x] inn í r.
    // Put an appropriate body of the loop here.
    // Remove one value from rest using
    //    var x :| x in rest;
    //    rest := rest-multiset{x};
    // and use Search to find the correct place
    // to insert [x] into r.

    // Remove variable from bag.
    var x :| x in rest;
    rest := rest-multiset{x};

    // Find the correct place to insert x and insert.
    var k := Search(r, x);
    r := r[..k]+[x]+r[k..];
  }

  return;
}