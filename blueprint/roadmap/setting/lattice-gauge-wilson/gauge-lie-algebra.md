# Lie algebra of a gauge group

Let $(n, G)$ be a gauge group, and identify each element of $G$ with its
matrix in $M_{n+1}(\mathbb C)$, the space of complex $(n+1)\times(n+1)$
matrices. Regard $M_{n+1}(\mathbb C)$ as a real vector space, real numbers
multiplying each entry. For $Y \in M_{n+1}(\mathbb C)$,
$\exp(Y) = \sum_{k \ge 0} Y^k/k!$ is the matrix exponential.

A matrix $X \in M_{n+1}(\mathbb C)$ **generates a one-parameter subgroup** of
$G$ when, for every real number $t$, the matrix $\exp(tX)$ is the matrix of an
element of $G$.

The **Lie algebra** $\mathfrak g$ of the gauge group is the real linear
subspace of $M_{n+1}(\mathbb C)$ whose elements are exactly these matrices:

$$\mathfrak g = \{X \in M_{n+1}(\mathbb C) : \exp(tX) \in G \text{ for every } t \in \mathbb R\}.$$

This set contains $0$ and is closed under addition and under multiplication
by real numbers, so it is a real linear subspace of $M_{n+1}(\mathbb C)$.
Regarded as a real vector space in its own right, $\mathfrak g$ has the
matrices in $\mathfrak g$ as its elements, with the addition and real scalar
multiplication of $M_{n+1}(\mathbb C)$.

The definition does not require $G$ to be connected.

## Depends on

- [Elements and matrices of a gauge group](group-elements-and-matrices.md)

## Sources

- [YM/Gauge ledger: Lie](../../../sources/lattice-gauge-wilson.md#lie)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
