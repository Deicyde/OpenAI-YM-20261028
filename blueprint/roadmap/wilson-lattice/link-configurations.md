# Link configurations

Let $(n, G, \mathfrak g)$ be a matrix gauge group, so that $G$ is a closed
subgroup of the group of unitary $(n+1)\times(n+1)$ complex matrices, and let
$M$ be a positive integer. Write $\Lambda_M = (\mathbb Z/M\mathbb Z)^4$ for the
periodic lattice of side $M$, whose sites have one coordinate modulo $M$ for
each axis $0, 1, 2, 3$. A **link** is a pair $(x, i)$ of a site
$x \in \Lambda_M$ and an axis $i \in \{0, 1, 2, 3\}$, read as the link leaving
$x$ along axis $i$. A **configuration** on $\Lambda_M$ with values in $G$ is a
map

$$U : \Lambda_M \times \{0, 1, 2, 3\} \to G, \qquad (x, i) \mapsto U(x, i),$$

which assigns an element of $G$ to every link. The configurations form the set
$G^{\Lambda_M \times \{0, 1, 2, 3\}}$ of all such maps, with no condition on
them. Wherever a topology on configurations is used, it is the product
topology, $G$ carrying the topology it inherits from the complex
$(n+1)\times(n+1)$ matrices with entrywise convergence.

## Depends on

- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Periodic lattice](periodic-lattice.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [PublicWilson.lean ledger: link configurations](../../sources/public-wilson.md#link-configurations)
