# Spacelike vectors

For a point $x = (x_0, x_1, x_2, x_3)$ of spacetime $\mathbb R^4$, write
$t(x) = x_3$ for its time, the last coordinate, $\vec x = (x_0, x_1, x_2)$ for
its spatial part, and $m(x) = t(x)^2 - \|\vec x\|^2$ for its Minkowski square,
with $\|\vec x\|$ the Euclidean norm of $\mathbb R^3$. The spacelike vectors
form the set of points of $\mathbb R^4$ whose Minkowski square is strictly
negative:

$$
\{ x \in \mathbb R^4 : m(x) < 0 \}
= \{ x \in \mathbb R^4 : x_3^2 < x_0^2 + x_1^2 + x_2^2 \}.
$$

A point is spacelike when it lies in this set. The inequality is strict.

## Depends on

- [Spacetime and space](spacetime-coordinates.md)
- [Minkowski square](minkowski-square.md)

## Sources

- [PublicTheory.lean ledger: spacelike vectors](../../sources/public-theory.md#spacelike-vectors)
