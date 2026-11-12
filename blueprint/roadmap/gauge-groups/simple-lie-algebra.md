# Simplicity of the gauge Lie algebra

Let $(n, G, \mathfrak g)$ be a matrix gauge group, so that $\mathfrak g$ is a
real linear subspace of the space $M_{n+1}(\mathbb C)$ of complex
$(n+1)\times(n+1)$ matrices, regarded as a real vector space. For matrices $X$
and $Y$, $XY - YX$ is their commutator, formed with matrix multiplication. The
gauge group is **simple** when both of the following hold:

1. there exist $X \in \mathfrak g$ and $Y \in \mathfrak g$ with
   $XY - YX \neq 0$;
2. every real linear subspace $\mathfrak i$ of $M_{n+1}(\mathbb C)$ such that
   $\mathfrak i \subseteq \mathfrak g$ and $XY - YX \in \mathfrak i$ for all
   $X \in \mathfrak g$ and all $Y \in \mathfrak i$ satisfies
   $\mathfrak i = \{0\}$ or $\mathfrak i = \mathfrak g$.

Simplicity is a condition on a gauge group, not further data. The source
describes it as real simplicity of the Lie algebra, including the nonabelian
condition: the first clause is the nonabelian condition, the Lie bracket is the
matrix commutator, and the subspaces $\mathfrak i$ of the second clause, the
ideals, are real linear subspaces. The condition is stated in terms of
$\mathfrak g$ alone and says nothing directly about $G$, such as whether it is
connected or what its centre is. Neither clause asserts that $\mathfrak g$
itself is closed under commutators.

## Depends on

- [Matrix gauge group](gauge-group.md)

## Sources

- [PublicTheory.lean ledger: simple Lie algebra](../../sources/public-theory.md#simple-lie-algebra)
- [Upstream description: the public challenge](../../sources/upstream-readme.md#the-public-challenge)
