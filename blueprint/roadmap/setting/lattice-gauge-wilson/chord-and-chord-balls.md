# Normalized chord and chord balls

Let $(n, G)$ be a gauge group, so that $G$ is a closed subgroup of the
unitary group $U(n+1)$, and identify each element $u \in G$ with its matrix
in $M_{n+1}(\mathbb C)$; $1$ is the identity matrix. For a matrix
$A \in M_{n+1}(\mathbb C)$ with entries $A_{ij}$, the Frobenius norm is

$$\|A\|_F = \Big(\sum_{i,j} |A_{ij}|^2\Big)^{1/2}.$$

The **normalized chord** of an element $u \in G$ is the real number

$$\chi(u) = \frac{\|u - 1\|_F}{\sqrt{n+1}}.$$

For every real number $r$, the **closed chord ball** of radius $r$ is the set

$$\{u \in G : \chi(u) \le r\}.$$

The norm in the chord is the Frobenius norm of the matrix $u - 1$, not its
operator norm, and the normalizing factor is the square root of the matrix
size $n+1$. The definition of the ball allows every real radius $r$ and
places no condition on it.

## Depends on

- [Elements and matrices of a gauge group](group-elements-and-matrices.md)

## Sources

- [YM/Gauge ledger: MatrixGroup](../../../sources/lattice-gauge-wilson.md#matrixgroup)
- [YM/Gauge ledger: Size](../../../sources/lattice-gauge-wilson.md#size)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
