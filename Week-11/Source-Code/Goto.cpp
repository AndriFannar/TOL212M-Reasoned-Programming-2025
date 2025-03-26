/*

Röksemdafærsla í C/C++.
Reglur fyrir goto.

Resoning in C/C++.
Rules for goto.

...
// P
if( C ) goto L;
// Q
...


...
// R
L:
// S
...


...
// T
goto L;
// false


1) P && !C ==> Q
2) P && C ==> S
3) R ==> S
4) T ==> S

*/

#include <iostream>

// Notkun: int k = search(a,n,x);
// Fyrir:  a vísar á fylki heiltalna í vaxandi röð
//         með n gildi. x er heiltala.
// Eftir:  0 <= k <= n,
//         a[0..k) < x <= a[k..n).
// Usage:  int k = search(a,n,x);
// Pre:    a refers to an ascending array of int
//         with n values. x is an int.
// Eftir:  0 <= k <= n,
//         a[0..k) < x <= a[k..n).
int search( int a[], int n, int x )
{
    ////////////////////////
    // a: | í vaxandi röð |
    //     ^               ^
    //     0               n
    ////////////////////////
    ////////////////////////
    // a: | ascending order |
    //     ^                 ^
    //     0                 n
    ////////////////////////
    int m, i=0, j=n;
start:
    ////////////////////////
    // a: | í vaxandi röð |
    //    | <x | ?? | >=x |
    //     ^    ^    ^     ^
    //     0    i    j     n
    ////////////////////////
    if( i == j ) goto end;
    m = i+(j-i)/2;
    if( a[m] < x )
        i = m+1;
    else
        j = m;
    goto start;
    // false
end:
    ////////////////////////
    // a: | í vaxandi röð |
    //    |  <x  |  >=x   |
    //     ^      ^        ^
    //     0      i        n
    ////////////////////////
    return i;
}

int main()
{
    //         0 1 2 3 4 5 6 7 8 9  10 11 12
    int a[] = {1,2,3,4,5,6,7,8,9,10,10,11,11};
    int k, n = sizeof(a)/sizeof(int);
    k = search(a,n,10);
    std::cout << k << std::endl;
    k = search(a,n,11);
    std::cout << k << std::endl;
    k = search(a,n,12);
    std::cout << k << std::endl;
}