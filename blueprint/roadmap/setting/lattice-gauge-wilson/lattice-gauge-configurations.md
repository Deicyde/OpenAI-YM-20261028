# Lattice gauge configurations

Let $(n, G)$ be a gauge group, so that $n$ is a natural number and $G$ is a
closed subgroup of the group of unitary $(n+1)\times(n+1)$ complex matrices, and
let $M$ be a side, a positive integer.

A **configuration** of the lattice of side $M$ is a link array over
$\mathbb Z/M\mathbb Z$ with values in $G$, that is, a map

$$
U : \Lambda_M \times \{0, 1, 2, 3\} \to G, \qquad (x, i) \mapsto U(x, i),
$$

where $\Lambda_M = (\mathbb Z/M\mathbb Z)^4$ is the set of sites of the
periodic lattice of side $M$. It assigns one element $U(x, i)$ of $G$ to every
site $x$ and every axis $i$, that is, to every positively oriented link
$(x, i)$, the link leaving $x$ in the positive direction of axis $i$. The
configurations form the set

$$
\mathcal C_M = G^{\Lambda_M \times \{0, 1, 2, 3\}}
$$

of all such maps. The definition imposes no condition on $U$.

## Depends on

- [Elements and matrices of a gauge group](group-elements-and-matrices.md)
- [Links and link arrays](links-and-link-arrays.md)
- [Sites of the periodic lattice](torus-sites.md)

## Sources

- [YM/Wilson ledger: Law](../../../sources/lattice-gauge-wilson.md#law)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
