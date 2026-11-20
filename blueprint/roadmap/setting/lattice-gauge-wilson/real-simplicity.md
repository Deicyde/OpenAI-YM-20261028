# Real simplicity of a gauge group

Let $(n, G)$ be a gauge group with Lie algebra $\mathfrak g$, a real linear
subspace of the space $M_{n+1}(\mathbb C)$ of complex $(n+1)\times(n+1)$
matrices, regarded as a real vector space. For matrices $X$ and $Y$,
$[X, Y] = XY - YX$ is their commutator, formed with matrix multiplication. The
gauge group is **simple** when both of the following hold:

1. there exist $X \in \mathfrak g$ and $Y \in \mathfrak g$ with
   $[X, Y] \neq 0$;
2. every real linear subspace $\mathfrak i$ of $M_{n+1}(\mathbb C)$ such that
   $\mathfrak i \subseteq \mathfrak g$ and $[X, Y] \in \mathfrak i$ for all
   $X \in \mathfrak g$ and all $Y \in \mathfrak i$ satisfies
   $\mathfrak i = \{0\}$ or $\mathfrak i = \mathfrak g$.

Simplicity is a condition on a gauge group, not further data. It is real
simplicity of $\mathfrak g$ together with a nonabelian clause. The first clause says
that $\mathfrak g$ is nonabelian, and the subspaces $\mathfrak i$ of the
second clause are the ideals of $\mathfrak g$, taken as real linear
subspaces. The condition is stated in
terms of $\mathfrak g$ alone and says nothing directly about $G$, such as
whether it is connected or what its centre is.

## Depends on

- [Lie algebra of a gauge group](gauge-lie-algebra.md)

## Sources

- [YM/Gauge ledger: Lie](../../../sources/lattice-gauge-wilson.md#lie)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
