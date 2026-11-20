# Links and link arrays

For every set $X$, an **edge** over $X$ is a pair $(x, i)$ of an element
$x \in X$ and an axis $i \in \{0, 1, 2, 3\}$. The edges over $X$ form the set
$X \times \{0, 1, 2, 3\}$.

For sets $R$ and $K$, a **link array** over $R$ with values in $K$ is a map

$$
f : R^4 \times \{0, 1, 2, 3\} \to K, \qquad (x, i) \mapsto f(x, i),
$$

that assigns an element of $K$ to every edge $(x, i)$ over the set $R^4$ of
four-component arrays over $R$. The link arrays over $R$ with values in $K$
form the set $K^{R^4 \times \{0, 1, 2, 3\}}$ of all such maps; no condition is
imposed on them.

The pair $(x, i)$ is read as the link leaving $x$ in the positive direction of
axis $i$. A link array has one value for each array $x$ and each axis $i$, that
is, one value per positively oriented link, and no separate value for the
reversed link.

## Depends on

- [Axes and four-component arrays](axes-and-arrays.md)

## Sources

- [YM/Lattice ledger: Path](../../../sources/lattice-gauge-wilson.md#path)
- [YM/Lattice ledger: Site](../../../sources/lattice-gauge-wilson.md#site)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
