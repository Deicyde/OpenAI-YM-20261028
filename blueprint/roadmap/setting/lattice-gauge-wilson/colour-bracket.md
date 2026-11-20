# Bracket in colour coordinates

Let $(n, G)$ be a gauge group with Lie algebra
$\mathfrak g \subseteq M_{n+1}(\mathbb C)$, let $\mathbb R^d$ be its colour
space, $d$ being its number of colours, let $X_c \in \mathfrak g$ be the colour matrix of a colour
$c \in \mathbb R^d$, and let $\Pi : M_{n+1}(\mathbb C) \to \mathbb R^d$ be
its colour projection, the orthogonal projection onto $\mathfrak g$ for the
real Frobenius inner product followed by the inverse of the colour frame.

The **colour bracket** of the gauge group sends two colours $c, c'$ to the
colour projection of the commutator of their colour matrices:

$$
\operatorname{ad}(c)\, c' = \Pi \big( X_c X_{c'} - X_{c'} X_c \big) \in \mathbb R^d ,
\qquad c, c' \in \mathbb R^d .
$$

It is real bilinear, and the definition is stated in that form: for every
colour $c$, $\operatorname{ad}(c) : \mathbb R^d \to \mathbb R^d$ is a real
linear map, and $c \mapsto \operatorname{ad}(c)$ is a real linear map from
$\mathbb R^d$ to the real linear maps of $\mathbb R^d$.

## Depends on

- [Projection of matrices onto colours](colour-projection.md)

## Sources

- [YM/Gauge ledger: Colors](../../../sources/lattice-gauge-wilson.md#colors)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
