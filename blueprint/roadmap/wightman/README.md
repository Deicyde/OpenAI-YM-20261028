# Wightman quantum field theory

One of the four properties the challenge asks of a continuum hierarchy is
Wightman reconstruction. In the words of the
[upstream description](../../sources/upstream-readme.md#wightman-reconstruction),
the selected phase has a normalized cyclic vacuum, faithful tempered fields on a
common dense domain, positive energy, a unique translation-invariant vacuum up
to scalar, covariance and spacelike locality, and the symmetry coordinates cover
every proper orthochronous affine Poincaré transformation and determine the
inverse pullback on test functions. In the formal statement a continuum
hierarchy carries a Wightman theory, and its
[reconstruction conditions](../continuum-hierarchy/reconstruction.md) require
that theory to satisfy the Wightman axioms W0–W3 and its field system to be
faithful. This chapter states these notions exactly as the challenge
formalizes them.
Spacetime is $\mathbb R^4$ with its Euclidean inner product and norm and with
time as the last coordinate, and the test functions of this chapter are the
Schwartz test functions, as in the chapter on
[spacetime, Lorentz symmetry and test functions](../spacetime/README.md).

A Wightman theory on a complex Hilbert space $H$, with a complex vector space
$L$ of field labels, consists of data and one compatibility condition. The data
are a field system, made of a common domain in $H$, a vacuum vector in it, and
smeared fields that turn a label and a Schwartz test function into a linear map
of the domain into itself; a conjugate-linear map on labels; a translation
representation on $H$; an energy–momentum measure, which assigns an operator on
$H$ to every subset of $\mathbb R^4$ and a finite measure on $\mathbb R^4$ to
every vector; and a Poincaré action on $H$, on labels and on test functions. The
Poincaré action is given on a set of symmetries carrying a unit, a product and a
topology, identified with the Poincaré coordinates by a homeomorphism; through
these coordinates its product and its action on test functions are fixed by the
ordinary affine action on spacetime. The compatibility condition says that the
pure translations among the symmetries act on $H$ as the translation
representation does.

The Wightman axioms are four conditions on such a theory. W0 ties the
translations to the energy–momentum measure, asks that the operator the measure
assigns to the complement of the closed forward light cone be zero, and asks
that every translation-invariant vector be a multiple of the vacuum. W1 consists
of the domain axioms and the adjoint axiom. W2, Poincaré covariance, asks that
the action on labels respect the unit and the product, and that the operators of
the Poincaré action map the domain into itself, fix the vacuum and transform the
smeared fields covariantly. W3 is local commutativity at spacelike separation.
Faithfulness, which asks every nonzero label to have a nonzero smeared field, is
a further condition outside W0–W3.

Several of these conditions are formulated differently from common textbook
versions, and the articles state the versions used here:

- the domain is exactly the linear span of the vectors the fields generate from
  the vacuum, with no closure;
- temperedness asks that, for a fixed label and a fixed vector of the domain,
  the vector obtained by applying the smeared field depend continuously, in the
  norm of $H$, on the Schwartz test function;
- W0 pairs momenta with translation vectors by the Euclidean dot product of
  $\mathbb R^4$, with a plus sign in the exponent;
- unitarity of the operators representing translations and Poincaré symmetries
  is formalized as preservation of norms;
- the action on labels is defined for all symmetries, translations included;
- local commutativity asks any two smeared fields with spacelike separated test
  functions to commute on the domain, with no sign or grading.

## Hilbert space, labels and fields

The basic data are a complex Hilbert space, whose inner product is
conjugate-linear in its first argument, and a complex vector space of field
labels with no further structure. A field system on them consists of a domain, a
vacuum and smeared fields, linear in the label and in the Schwartz test
function. Finite words of label and test-function pairs generate vectors from
the vacuum, and the vacuum expectation value of an ordered product of smeared
fields is the inner product of the vacuum with such a vector.

- [Hilbert space and bounded operators](hilbert-space.md)
- [Field labels](field-labels.md)
- [Field system](field-system.md)
- [Vectors generated from the vacuum](field-vectors.md)
- [Vacuum expectation values](vacuum-expectation-values.md)

## Conditions on a field system

Four conditions concern a field system; the adjoint axiom also involves a
conjugate-linear map on labels. The domain axioms normalize the vacuum, make
the domain dense and equal to the span of the generated vectors,
and make the fields tempered. The adjoint axiom pairs each smeared field with
the field of the adjoint label, smeared with the complex conjugate test
function. Local commutativity makes smeared fields with spacelike separated test
functions commute on the domain, and faithfulness gives every nonzero label a
smeared field that is not zero.

- [Domain axioms](domain-axioms.md)
- [Adjoint axiom](adjoint-axiom.md)
- [Local commutativity](local-commutativity.md)
- [Faithful field system](faithful-fields.md)

## Translations, spectrum and Poincaré symmetry

Translations of $\mathbb R^4$ act on $H$ by a strongly continuous,
norm-preserving representation. The energy–momentum measure assigns an operator
to every subset of $\mathbb R^4$, subject to conditions on Borel sets, and a
finite Borel measure to every vector, whose value on each Borel set is the
inner product of that vector with its image under the operator assigned to
the set. The Poincaré action
acts on $H$, on labels and on Schwartz test functions. In its coordinates the
unit is the identity transformation, the product is the composition of affine
maps of $\mathbb R^4$, the pure translation by a vector is the translation by
that vector, and a symmetry acts on a test function by composing it with the
inverse of its affine map.

- [Translation representation](translation-representation.md)
- [Energy–momentum measure](energy-momentum-measure.md)
- [Poincaré action](poincare-action.md)

## Wightman theories and the axioms W0–W3

A Wightman theory gathers a field system, a conjugate-linear map on labels, a
translation representation, an energy–momentum measure and a Poincaré action
whose pure translations act on $H$ as the translation representation does. The
Wightman axioms consist of the four conditions W0, W1, W2 and W3 and nothing
more.

- [Wightman theory data](wightman-theory.md)
- [Axiom W0: spectrum condition and unique vacuum](axiom-w0.md)
- [Axiom W1: fields on a common dense domain](axiom-w1.md)
- [Axiom W2: Poincaré covariance](axiom-w2.md)
- [Axiom W3: locality](axiom-w3.md)
- [The Wightman axioms](wightman-axioms.md)
