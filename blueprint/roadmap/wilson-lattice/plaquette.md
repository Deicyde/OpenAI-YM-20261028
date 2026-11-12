# Plaquette

Let $(n, G, \mathfrak g)$ be a matrix gauge group, so that $G$ is a group of
unitary $(n+1)\times(n+1)$ complex matrices, let $M$ be a positive integer, and
let $U$ be a configuration on the periodic lattice
$\Lambda_M = (\mathbb Z/M\mathbb Z)^4$ with values in $G$: an element
$U(x, i) \in G$ for every site $x \in \Lambda_M$ and every axis
$i \in \{0, 1, 2, 3\}$. For an axis $i$, let $e_i \in \Lambda_M$ be the site
with coordinate $1$ on axis $i$ and $0$ on the other three axes. For a site $x$
and two axes $i$ and $j$, equal or not, the **plaquette** of $U$ at $x$ in the
directions $i, j$ is the element

$$U_{x;ij} = U(x, i)\, U(x + e_i, j)\, U(x + e_j, i)^{-1}\, U(x, j)^{-1}$$

of $G$, where products and inverses are taken in $G$ and sites are added
coordinatewise modulo $M$.

## Depends on

- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Link configurations](link-configurations.md)
- [Periodic lattice](periodic-lattice.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [PublicWilson.lean ledger: plaquette](../../sources/public-wilson.md#plaquette)
