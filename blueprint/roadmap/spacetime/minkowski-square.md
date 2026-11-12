# Minkowski square

For a point $x = (x_0, x_1, x_2, x_3)$ of spacetime $\mathbb R^4$, write
$t(x) = x_3$ for its time, the last coordinate, and
$\vec x = (x_0, x_1, x_2) \in \mathbb R^3$ for its spatial part. The Minkowski
square is the function $m : \mathbb R^4 \to \mathbb R$ given by

$$
m(x) = t(x)^2 - \|\vec x\|^2 = x_3^2 - x_0^2 - x_1^2 - x_2^2,
$$

where $\|\vec x\|$ is the Euclidean norm of $\mathbb R^3$. The time coordinate
enters with a plus sign and the three spatial coordinates with minus signs.

## Depends on

- [Spacetime and space](spacetime-coordinates.md)

## Sources

- [PublicTheory.lean ledger: Minkowski square](../../sources/public-theory.md#minkowski-square)
