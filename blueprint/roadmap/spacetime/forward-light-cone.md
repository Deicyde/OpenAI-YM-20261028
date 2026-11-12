# Closed forward light cone

For a point $x = (x_0, x_1, x_2, x_3)$ of spacetime $\mathbb R^4$, write
$t(x) = x_3$ for its time, the last coordinate, and
$\vec x = (x_0, x_1, x_2) \in \mathbb R^3$ for its spatial part. The closed
forward light cone is the set of points of $\mathbb R^4$ whose spatial part has
Euclidean norm at most their time:

$$
\overline{V}_+
= \{ x \in \mathbb R^4 : \|\vec x\| \le t(x) \}
= \Big\{ x \in \mathbb R^4 : \big( x_0^2 + x_1^2 + x_2^2 \big)^{1/2} \le x_3 \Big\}.
$$

Time is the last coordinate here, and the norm of the spatial part is the
Euclidean norm of $\mathbb R^3$.

## Depends on

- [Spacetime and space](spacetime-coordinates.md)

## Sources

- [PublicTheory.lean ledger: forward light cone](../../sources/public-theory.md#forward-light-cone)
