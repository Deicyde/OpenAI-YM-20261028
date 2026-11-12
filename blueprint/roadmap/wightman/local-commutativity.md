# Local commutativity

Let $H$ be a Hilbert space, $L$ a space of field labels,
$\mathcal S(\mathbb R^4)$ the space of Schwartz test functions
$f : \mathbb R^4 \to \mathbb C$ on spacetime $\mathbb R^4$, whose last
coordinate is time, and $(D, \Omega, \varphi)$ a field system on $H$ and $L$,
with domain $D$, vacuum $\Omega$ and smeared fields $\varphi(a,f) : D \to D$.
The closed support of a function on $\mathbb R^4$ is the closure of the set of
points where it is not zero. Two Schwartz test functions $f$ and $g$, in this
order, are spacelike separated when, for every point $x$ of the closed support
of $f$ and every point $y$ of the closed support of $g$, the vector
$v = x - y = (v_0, v_1, v_2, v_3)$ is spacelike, that is,
$v_3^2 - (v_0^2 + v_1^2 + v_2^2) < 0$.

The field system **satisfies local commutativity** when

$$
\varphi(a,f)\,\varphi(b,g)\,\psi = \varphi(b,g)\,\varphi(a,f)\,\psi
$$

for all labels $a, b \in L$, all Schwartz test functions
$f, g \in \mathcal S(\mathbb R^4)$ such that $f$ and $g$ are spacelike
separated, and every vector $\psi \in D$. Here
$\varphi(a,f)\,\varphi(b,g)\,\psi$ is the vector obtained by applying
$\varphi(b,g)$ to $\psi$ and then $\varphi(a,f)$ to the result.

Local commutativity is a condition on the field system alone; it involves no
further data. It asks the two smeared fields to commute on $D$, for every pair
of labels, with no sign factor, grading or anticommutator.

## Depends on

- [Field system](../wightman/field-system.md)
- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Spacelike separated Schwartz test functions](../spacetime/spacelike-separated-tests.md)

## Sources

- [PublicTheory.lean ledger: local commutativity](../../sources/public-theory.md#local-commutativity)
