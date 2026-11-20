# Gauge group in a unitary representation

For a natural number $n$ ($n = 0, 1, 2, \dots$), write $M_{n+1}(\mathbb C)$
for the set of complex $(n+1)\times(n+1)$ matrices, with matrix
multiplication and the topology of entrywise convergence. For a matrix $A$,
$A^*$ is its conjugate transpose, and $1$ is the identity matrix. The unitary
group is

$$U(n+1) = \{A \in M_{n+1}(\mathbb C) : A^*A = 1 \text{ and } AA^* = 1\},$$

a group under matrix multiplication, in which the inverse of $A$ is $A^*$,
with the subspace topology of $M_{n+1}(\mathbb C)$.

A **gauge group** $(n, G)$ consists of the following three components, two of
them data and one a condition on the data:

1. a natural number $n$ (data); the matrices of the gauge group have size
   $(n+1)\times(n+1)$, so $n = 0$ gives $1\times 1$ matrices;
2. a subgroup $G$ of $U(n+1)$ (data);
3. $G$ is a closed subset of $U(n+1)$ (condition).

Nothing else is part of a gauge group. Thus a gauge group is a compact
matrix group in a fixed faithful unitary representation: the
representation is the inclusion $G \subseteq U(n+1)$, so the matrices are part
of the data, and $G$ is given as a set of unitary matrices. The definition
states no compactness condition of its own; its only topological condition is
that $G$ be closed in $U(n+1)$. It has no Lie algebra among its components, and
it does not require $G$ to be connected, and it imposes no simplicity condition.

## Depends on

This node has no prerequisites.

## Sources

- [YM/Gauge ledger: MatrixGroup](../../../sources/lattice-gauge-wilson.md#matrixgroup)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
