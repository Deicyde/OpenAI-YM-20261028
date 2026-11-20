# Haar probability measure of a gauge group

Let $(n, G)$ be a gauge group, so that $G$ is a closed subgroup of the
unitary group $U(n+1)$, and identify each element of $G$ with its matrix in
$M_{n+1}(\mathbb C)$. Give $G$ the topology it inherits from
$M_{n+1}(\mathbb C)$ with entrywise convergence (equivalently, from
$U(n+1)$). With matrix multiplication, $G$ is a topological group, and it is
compact, being a closed subset of the compact group $U(n+1)$.

The measurable sets of $G$ are its **Borel sets**: the σ-algebra on $G$ is
the smallest σ-algebra containing the open subsets of $G$.

The whole group $G$, taken as a subset of itself, is compact and has
nonempty interior (its interior is $G$, which contains the identity matrix
$1$). The **Haar probability measure** $h_G$ is the left Haar measure of $G$
scaled so that this compact set has measure $1$, that is, $h_G(G) = 1$.

For a compact set $K \subseteq G$ and an open set $V \subseteq G$ containing
$1$, let $[K : V]$ be the least number of left translates $uV$ ($u \in G$)
that cover $K$ (finitely many translates cover $K$, since $K$ is compact).
Haar's construction with reference set $G$ chooses one function $c$ on the
compact subsets of $G$ that lies, for every open neighbourhood $W$ of $1$, in
the closure, for the topology of pointwise convergence in the space of real
functions on the compact subsets of $G$, of the set of functions $K \mapsto [K : V]/[G : V]$ with $V$ an
open neighbourhood of $1$ contained in $W$. This function is a content
(it is monotone and subadditive, and additive on disjoint compact sets), and
it induces a Borel measure $m$ on $G$: for a Borel set $A$, $m(A)$ is the
infimum, over open sets $O \supseteq A$, of the supremum of $c(K)$ over
compact sets $K \subseteq O$ (on a compact set $K$ this value is at least
$c(K)$). Then

$$h_G = \frac{1}{m(G)}\, m .$$

## Depends on

- [Elements and matrices of a gauge group](group-elements-and-matrices.md)

## Sources

- [YM/Gauge ledger: MatrixGroup](../../../sources/lattice-gauge-wilson.md#matrixgroup)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
