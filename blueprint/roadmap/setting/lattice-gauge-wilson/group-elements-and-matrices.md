# Elements and matrices of a gauge group

Let $(n, G)$ be a gauge group, so that $G$ is a closed subgroup of the unitary
group $U(n+1)$, which is itself a subset of the space $M_{n+1}(\mathbb C)$ of
complex $(n+1)\times(n+1)$ matrices. The following are names attached to the
gauge group; none of them imposes a further condition.

1. The **dimension of the defining representation** is $n+1$, the size of the
   matrices. It is not the number of colours, which is the real dimension of
   the Lie algebra of the gauge group.
2. The **matrix space** of the gauge group is $M_{n+1}(\mathbb C)$, with its
   usual operations (addition, matrix multiplication, conjugate transpose,
   multiplication by real and by complex numbers) and the topology of entrywise
   convergence.
3. The **link state space** is the group $G$ itself: its elements are the
   elements of $G$, with the group structure of $G$ and the topology that $G$
   inherits from $U(n+1)$. It is the set in which the variables attached to
   lattice links take their values.
4. The **matrix** of an element $u \in G$ is $u$ itself, regarded as an
   element of $M_{n+1}(\mathbb C)$ through the inclusions
   $G \subseteq U(n+1) \subseteq M_{n+1}(\mathbb C)$.

In this chapter each element $u$ of $G$ is identified with its matrix, so that
$uv$, $u^*$ and $u - 1$ are computed in $M_{n+1}(\mathbb C)$.

## Depends on

- [Gauge group in a unitary representation](gauge-group-in-representation.md)

## Sources

- [YM/Gauge ledger: MatrixGroup](../../../sources/lattice-gauge-wilson.md#matrixgroup)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
