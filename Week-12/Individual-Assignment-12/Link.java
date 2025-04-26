// Tilvik af Link<E> eru hlekkir í keðju sem hver um
// sig inniheldur tilvísun í tilvik af klasa af tagi E.
// Instances of Link<E> are links in a chain that each
// contains a reference to an instance of class E.

public class Link<E>
{
	public E head;
	public Link<E> tail;
}

// Skilgreining á löglegri keðju:
//   1) null er lögleg keðja af tagi Link<E> með núll hlekki og tómri
//      hlekkjarunu [].
//   2) Ef x er lögleg keðja af tagi Link<E> með N hlekki og hlekkjarunu
//      [h_0,...,h_{N-1}] og y vísar á hlekk af tagi Link<E> með
//      y.tail == x þá er y lögleg hlekkjaruna af tagi Link<E> með N+1
//      hlekki og hlekkjarunu [y,h_0,...,h_{N-1}].
//   3) Engin önnur gildi eru löglegar keðjur af tagi Link<E>.

// Takið eftir að allar löglegar keðjur eru endanlegar og eru ekki
// tengdar í hring neins staðar.

// Setning 1: Ef x er lögleg keðja með hlekkjarunu [h_0,...,h_{N-1}] þá eru
// allir hlekkirnir mismunandi hlutir, þ.e. fyrir 0 <= I < J < N gildir að
// h_I != h_J, þ.e. h_I er ekki sami hlutur og h_J.

// Setning 2: Ef x er lögleg keðja með ekki-tóma hlekkjarunu [h_0,...,h_{N-1}]
// þá er h_{N-1}.tail == null.

// Setning 3: Ef x er lögleg keðja með hlekkjarunu [h_0,...,h_{N-1}] þá gildir
// fyrir öll I þ.a. 0 <= I < N-1 að h_I.tail == h_{I+1}.

// Definition of a legal chain:
//   1) null is a legal chain of type Link<E> with zero links and and an empty
//      sequence of links [].
//   2) If x is a legal chain of type Link<E> with N links and a sequence of
//      links [h_0,...,h_{N-1}] and y refers to a link of type Link<E> with
//      y.tail == x then y is a legal chain of type Link<E> with N+1 links
//      and the sequence of links [y,h_0,...,h_{N-1}].
//   3) No other values are legal chains of type Link<E>.

// Note that all legal chains are finite and they are not circular.

// Theorem 1: If x is a legal chain with the sequence of links [h_0,...,h_{N-1}]
// then all the links are distinct objects, i.e. for 0 <= I < J < N we have
// allir hlekkirnir mismunandi hlutir, þ.e. fyrir 0 <= I < J < N gildir að
// h_I != h_J, i.e. h_I is not the same object as h_J.

// Theorem 2: If x is a legal chain with a non-empty sequence of linke [h_0,...,h_{N-1}]
// then h_{N-1}.tail == null.

// Theorem 3: If x is a legal chain with the sequence of links  [h_0,...,h_{N-1}] then
// for all I such that 0 <= I < N-1 we have h_I.tail == h_{I+1}.
