# Adjoint axiom

Let $H$ be a Hilbert space whose inner product $\langle\cdot,\cdot\rangle$ is
conjugate-linear in its first argument and linear in its second, $L$ a space of
field labels, $\mathcal S(\mathbb R^4)$ the space of Schwartz test functions
$f : \mathbb R^4 \to \mathbb C$, and $(D, \Omega, \varphi)$ a field system on
$H$ and $L$, with domain $D$, vacuum $\Omega$ and smeared fields
$\varphi(a,f) : D \to D$. For $f \in \mathcal S(\mathbb R^4)$, let
$\bar f \in \mathcal S(\mathbb R^4)$ be its complex conjugate,
$\bar f(x) = \overline{f(x)}$ for every $x \in \mathbb R^4$.

Let $a \mapsto a^\dagger$ be a conjugate-linear map from $L$ to $L$: for all
labels $a, b \in L$ and complex numbers $c$,

$$
(a + b)^\dagger = a^\dagger + b^\dagger, \qquad (c\,a)^\dagger = \bar c\,a^\dagger ,
$$

where $\bar c$ is the complex conjugate of $c$. The field system **satisfies the
adjoint axiom** for $\dagger$ when

$$
\big\langle \varphi(a,f)\,\psi,\ \chi \big\rangle
= \big\langle \psi,\ \varphi(a^\dagger, \bar f)\,\chi \big\rangle
$$

for every label $a \in L$, every Schwartz test function
$f \in \mathcal S(\mathbb R^4)$ and all vectors $\psi, \chi \in D$, both inner
products being taken in $H$.

The adjoint axiom is a condition on the field system together with the map
$\dagger$, which is given with it; the condition supplies no further data. The
map $\dagger$ is required only to be conjugate-linear: it need not be an
involution. The identity is required only for vectors $\psi$ and $\chi$ of the
domain $D$.

## Depends on

- [Field system](../wightman/field-system.md)
- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Complex conjugate of a test function](../spacetime/conjugate-test-function.md)

## Sources

- [PublicTheory.lean ledger: adjoint axiom](../../sources/public-theory.md#adjoint-axiom)
