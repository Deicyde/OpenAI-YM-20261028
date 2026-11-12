# Wilson action

Let $(n, G, \mathfrak g)$ be a matrix gauge group, so that $G$ is a group of
unitary $(n+1)\times(n+1)$ complex matrices, and let $M$ be a positive integer.
The **plaquette orientations** are the pairs $(i, j)$ of axes
$i, j \in \{0, 1, 2, 3\}$ with $i < j$. The **Wilson action** of a
configuration $U$ on the periodic lattice $\Lambda_M = (\mathbb Z/M\mathbb Z)^4$
with values in $G$ is the real number

$$S(U) = \sum_{x \in \Lambda_M} \sum_{0 \le i < j \le 3} \left(1 - \frac{\operatorname{Re} \operatorname{tr} U_{x;ij}}{n+1}\right),$$

where the outer sum runs over all sites $x$ and the inner sum over all
plaquette orientations $(i, j)$; $U_{x;ij} \in G$ is the plaquette of $U$ at
$x$ in the directions $i, j$; $\operatorname{tr}$ is the trace, the sum of the
diagonal entries, of a complex $(n+1)\times(n+1)$ matrix; and
$\operatorname{Re}$ is the real part. The real part of the trace is divided by
the matrix size $n+1$, and the action contains no coupling constant.

## Depends on

- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Link configurations](link-configurations.md)
- [Periodic lattice](periodic-lattice.md)
- [Plaquette](plaquette.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [PublicWilson.lean ledger: Wilson action](../../sources/public-wilson.md#wilson-action)
- [Upstream description: Wilson origin](../../sources/upstream-readme.md#wilson-origin)
