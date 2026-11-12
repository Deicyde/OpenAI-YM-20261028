# Spacetime and space

Spacetime has four axes, numbered $0, 1, 2, 3$, and space has three, numbered
$0, 1, 2$. The time axis is axis $3$, the last axis of spacetime.

Spacetime is the Euclidean space $\mathbb R^4$: its points are the quadruples
$x = (x_0, x_1, x_2, x_3)$ of real numbers, one coordinate for each axis, with
the Euclidean inner product and norm

$$
\langle x, y \rangle = \sum_{a=0}^{3} x_a y_a,
\qquad
\|x\| = \Big( \sum_{a=0}^{3} x_a^2 \Big)^{1/2},
$$

and the distance $\|x - y\|$. Space is the Euclidean space $\mathbb R^3$: its
points are the triples $p = (p_0, p_1, p_2)$ of real numbers, one coordinate
for each axis of space, with the inner product $\sum_{i=0}^{2} p_i q_i$, the
norm $\|p\| = \big( \sum_{i=0}^{2} p_i^2 \big)^{1/2}$ and the distance
$\|p - q\|$. Both carry the topology of their norm, its Borel sets and
Lebesgue measure.

The time of a point $x$ of spacetime is its last coordinate, $t(x) = x_3$, and
its spatial part is the point $\vec x = (x_0, x_1, x_2)$ of space formed by its
first three coordinates. Time is thus the last coordinate, and the inner
product, norm and distance of spacetime are the Euclidean ones, not those of
Minkowski space.

## Depends on

This node has no prerequisites.

## Sources

- [PublicTheory.lean ledger: spacetime coordinates](../../sources/public-theory.md#spacetime-coordinates)
- [ChallengeSpec.lean ledger: euclidean configurations](../../sources/challenge-spec.md#euclidean-configurations)
