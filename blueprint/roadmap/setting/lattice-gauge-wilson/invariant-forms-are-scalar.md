# Invariant symmetric forms on the colour space are multiples of the standard inner product

Let $(n, G)$ be a gauge group with Lie algebra
$\mathfrak g \subseteq M_{n+1}(\mathbb C)$, let $d$ be its number of colours,
let $\mathbb R^d$ be its colour space with the standard inner product
$\langle c, c' \rangle = \sum_k c_k c'_k$, and let
$\operatorname{ad}(c)\, c' = \Pi(X_c X_{c'} - X_{c'} X_c)$ be its colour
bracket, where $X_c$ is the colour matrix of a colour $c$ and $\Pi$ is the
colour projection.

**Theorem.** Suppose that the gauge group is simple: some two elements of
$\mathfrak g$ do not commute, and every real linear subspace of
$M_{n+1}(\mathbb C)$ contained in $\mathfrak g$ that contains $XY - YX$ for
all $X \in \mathfrak g$ and all $Y$ in the subspace is $\{0\}$ or
$\mathfrak g$. Let $B : \mathbb R^d \times \mathbb R^d \to \mathbb R$ be a
real bilinear form such that

1. $B$ is symmetric: $B(c, c') = B(c', c)$ for all $c, c' \in \mathbb R^d$;
2. $B$ is invariant under the colour bracket:

    $$
    B\big(\operatorname{ad}(c)\, c',\ c''\big) = - B\big(c',\ \operatorname{ad}(c)\, c''\big)
    \qquad \text{for all } c, c', c'' \in \mathbb R^d .
    $$

Then there is a real number $\lambda$ such that

$$
B(c, c') = \lambda \, \langle c, c' \rangle \qquad \text{for all } c, c' \in \mathbb R^d .
$$

The theorem does not identify $\lambda$ and claims nothing about its sign. Its
only hypotheses are the simplicity of the gauge group and the two conditions
on $B$.

## Depends on

- [Bracket in colour coordinates](colour-bracket.md)
- [Real simplicity of a gauge group](real-simplicity.md)

## Sources

- [YM/Gauge ledger: Casimir](../../../sources/lattice-gauge-wilson.md#casimir)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
