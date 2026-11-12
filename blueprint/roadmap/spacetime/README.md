# Spacetime, Lorentz symmetry and test functions

This chapter fixes the conventions that every later chapter shares: the points
of spacetime and their coordinates, the pieces of Minkowski geometry the
challenge uses, the proper orthochronous Lorentz transformations and
coordinates for the Poincaré group, the Schwartz test functions with which
fields are smeared, and the configurations of finitely many points at which
correlations are evaluated, together with the test functions on separated
configurations.

Spacetime is $\mathbb R^4$ with its Euclidean inner product and norm, and time
is the last of its four coordinates: a point is $x = (x_0, x_1, x_2, x_3)$, its
time is $x_3$, and its spatial part is $(x_0, x_1, x_2) \in \mathbb R^3$.
[The source](../../sources/public-theory.md#forward-light-cone) states this
convention when it defines the closed forward light cone "in the convention
where time is the final coordinate". The only norm, inner
product and distance on spacetime in this book are the Euclidean ones: they
measure the decay of Schwartz test functions, enter the characteristic function
in [axiom W0](../wightman/axiom-w0.md), and give every distance between points
in the [operator product expansion](../operator-product-expansion/README.md).
Minkowski geometry enters only through three definitions: the Minkowski square
$x_3^2 - x_0^2 - x_1^2 - x_2^2$, the closed forward light cone and the set of
spacelike vectors. The same $\mathbb R^4$ also holds the Euclidean
configurations at which the continuum hierarchy's correlations are evaluated,
and the [reconstruction](../continuum-hierarchy/reconstruction.md) reads the
last coordinate of each of their points as an imaginary time.

[The source](../../sources/public-theory.md#lorentz-and-poincare) describes
the proper orthochronous Lorentz transformations as the "proper,
time-orientation-preserving linear transformations of Minkowski space". They
are the invertible continuous linear maps of $\mathbb R^4$ with
determinant one that preserve the Minkowski square and send a vector into the
closed forward light cone exactly when the vector lies in it. A pair of such a
transformation and a vector of $\mathbb R^4$ is what the source calls
"standard coordinates on the full proper orthochronous Poincaré group". This
chapter defines only the set of these pairs and its topology. The
multiplication of symmetries, their action on states, field labels and test
functions, and the requirement that the coordinates cover every proper
orthochronous Lorentz transformation and translation belong to the
[Poincaré action](../wightman/poincare-action.md) of the Wightman chapter. In
the words of the
[upstream description](../../sources/upstream-readme.md#wightman-reconstruction),
the symmetry coordinates "cover every proper orthochronous affine Poincaré
transformation and determine the inverse pullback on test functions".

"Test function" has two meanings in this book, kept apart by name. A
*Schwartz test function* is a smooth complex-valued function on $\mathbb R^4$
all of whose derivatives stay bounded after multiplication by any power of the
Euclidean norm. The Schwartz test functions form the Schwartz space, and
continuity in a test function always refers to its seminorm topology. The
fields of a Wightman theory are smeared with Schwartz test functions, and this
chapter also defines their complex conjugates and the spacelike separation of
two of them, which the adjoint axiom and local commutativity use. A
*separated test function* is a smooth complex-valued function with compact
support on configurations of $n$ points whose support avoids every collision of
two points; the
[ordered continuum limit](../wilson-lattice/ordered-continuum-limit.md) of the
lattice moments is tested against separated test functions. The first kind
lives on spacetime and is defined by decay conditions, the second lives on
configurations and is defined by a support condition.

A configuration of $n$ points is an ordered tuple $(x_0, \dots, x_{n-1})$ of
points of $\mathbb R^4$, with the Euclidean norm of $\mathbb R^{4n}$. It is
separated when its points are pairwise distinct, and the separated
configurations form an open set, the complement of the collision diagonals
$x_i = x_j$ with $i \ne j$. The continuum hierarchy's correlations are
functions on configurations, and the reconstruction asks, at separated
configurations, for their permutation symmetry, their smoothness, their
continuous dependence on the character, and that their integral over the
characters be the unselected correlation. In the words of the
[upstream description](../../sources/upstream-readme.md#all-orders-separated-ope),
"permutation symmetry and smoothness hold off the collision diagonals".

## Coordinates

The axes of spacetime are numbered $0, 1, 2, 3$ and those of space $0, 1, 2$;
the time axis is $3$. A point of spacetime has a time, its last coordinate,
and a spatial part, the point of $\mathbb R^3$ formed by its first three
coordinates.

- [Spacetime and space](spacetime-coordinates.md)

## Minkowski geometry

The Minkowski square of a point is its time squared minus the squared
Euclidean norm of its spatial part. The closed forward light cone is defined by
its own inequality, the norm of the spatial part being at most the time, rather
than through the Minkowski square, and a vector is spacelike when its Minkowski
square is strictly negative. The proper orthochronous Lorentz transformations
are the invertible continuous linear maps of $\mathbb R^4$ with determinant one
that preserve the Minkowski square and send a vector into the cone exactly when
the vector lies in it, and Poincaré coordinates pair them with vectors of
$\mathbb R^4$. The cone returns in the spectrum condition
of axiom W0, and spacelike vectors in local commutativity.

- [Minkowski square](minkowski-square.md)
- [Closed forward light cone](forward-light-cone.md)
- [Spacelike vectors](spacelike-vectors.md)
- [Proper orthochronous Lorentz transformations and Poincaré coordinates](lorentz-and-poincare.md)

## Test functions on spacetime

The Schwartz test functions are the test functions of the Wightman theory.
Their complex conjugation, in
[the source's](../../sources/public-theory.md#conjugate-test-function) words
the "pointwise complex conjugation of a Schwartz test function", is a
continuous real-linear map of
the Schwartz space to itself and appears in the
[adjoint axiom](../wightman/adjoint-axiom.md). Two Schwartz test functions are
spacelike separated when the difference of any point of the closed support of
the first and any point of the closed support of the second is spacelike;
[the source](../../sources/public-theory.md#spacelike-separated-tests) calls
such functions "causally disjoint", and
[local commutativity](../wightman/local-commutativity.md) requires the fields
smeared with two such functions to commute.

- [Schwartz test functions](schwartz-test-functions.md)
- [Complex conjugate of a test function](conjugate-test-function.md)
- [Spacelike separated Schwartz test functions](spacelike-separated-tests.md)

## Configurations of points

Configurations of $n$ points carry the Euclidean structure of
$\mathbb R^{4n}$. The separated configurations, those whose points are
pairwise distinct, form an open set, and the separated test functions are the
smooth complex-valued functions with compact support inside it.

- [Configurations of n points](point-configurations.md)
- [Separated configurations](separated-configurations.md)
- [Test functions on separated configurations](separated-test-functions.md)
