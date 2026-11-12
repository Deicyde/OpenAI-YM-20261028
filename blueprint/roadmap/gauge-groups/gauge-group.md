# Matrix gauge group

For a natural number $n$ ($n = 0, 1, 2, \dots$), write $M_{n+1}(\mathbb C)$
for the set of complex $(n+1)\times(n+1)$ matrices, with matrix addition and
multiplication, real scalars multiplying each entry, and the topology of
entrywise convergence. For a matrix $A$, $A^*$ is its conjugate transpose, and
$1$ is the identity matrix. The unitary group is

$$U(n+1) = \{A \in M_{n+1}(\mathbb C) : A^*A = 1 \text{ and } AA^* = 1\},$$

a group under matrix multiplication, with the subspace topology; the source
calls it the fixed faithful unitary representation used to describe a gauge
group. For $Y \in M_{n+1}(\mathbb C)$, $\exp(Y) = \sum_{k \ge 0} Y^k/k!$ is
the matrix exponential.

A **matrix gauge group** $(n, G, \mathfrak g)$ consists of the following five
components, three of them data and two of them conditions on the data:

1. a natural number $n$ (data); the matrices of the gauge group have size
   $(n+1)\times(n+1)$, so $n = 0$ gives $1\times 1$ matrices;
2. a subgroup $G$ of $U(n+1)$ (data);
3. $G$ is a closed subset of $U(n+1)$ (condition);
4. a real linear subspace $\mathfrak g$ of $M_{n+1}(\mathbb C)$, the latter
   regarded as a real vector space (data);
5. for every $X \in M_{n+1}(\mathbb C)$, $X \in \mathfrak g$ if and only if
   $\exp(tX) \in G$ for every real number $t$ (condition).

The last condition says that $\mathfrak g$ consists exactly of the matrices $X$
whose real one-parameter exponentials $\exp(tX)$, $t \in \mathbb R$, all lie
in $G$; the source calls $\mathfrak g$ the one-parameter Lie algebra of the
gauge group, and this condition is what keeps it from being arbitrary. The
matrix realization is part of the data: $G$ is given as a set of unitary
matrices. The source calls these groups compact; the definition states no
compactness condition of its own, and its only topological condition is that
$G$ be closed in $U(n+1)$. The definition does not require $G$ to be
connected, and it does not separately require $\mathfrak g$ to consist of
skew-Hermitian matrices or to be closed under commutators.

## Depends on

This node has no prerequisites.

## Sources

- [PublicTheory.lean ledger: gauge group](../../sources/public-theory.md#gauge-group)
- [Upstream description: the public challenge](../../sources/upstream-readme.md#the-public-challenge)
