# Translation representation

Let $H$ be a Hilbert space with norm $\lVert\cdot\rVert$, and let spacetime be
$\mathbb R^4$ with its Euclidean norm and topology. A bounded operator on $H$ is
a continuous complex-linear map $H \to H$; $1$ denotes the identity operator,
and $ST$ the composite of bounded operators $S$ and $T$, with $T$ applied first.

A **translation representation** on $H$ consists of one piece of data, a
bounded operator $U(x)$ on $H$ for every vector $x \in \mathbb R^4$, that is, a
map $x \mapsto U(x)$ from $\mathbb R^4$ to the bounded operators on $H$. It is
subject to four conditions:

1. *Unit:* $U(0) = 1$.
2. *Composition:* $U(x)\,U(y) = U(x + y)$ for all $x, y \in \mathbb R^4$.
3. *Norm preservation:* $\lVert U(x)\,\psi \rVert = \lVert \psi \rVert$ for
   every $x \in \mathbb R^4$ and every $\psi \in H$.
4. *Strong continuity:* for every $\psi \in H$, the map $x \mapsto U(x)\,\psi$
   from $\mathbb R^4$ to $H$ is continuous, for the Euclidean topology of
   $\mathbb R^4$ and the norm topology of $H$.

The source describes this structure as "a strongly continuous unitary
representation of spacetime translations". The condition it calls unitarity is
the norm preservation of condition 3.

## Depends on

- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [PublicTheory.lean ledger: translation representation](../../sources/public-theory.md#translation-representation)
