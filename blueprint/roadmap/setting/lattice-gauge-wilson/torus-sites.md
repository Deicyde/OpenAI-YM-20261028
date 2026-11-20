# Sites of the periodic lattice

A **side** is a positive integer $M$; the side $M = 1$ is included. For a side
$M$, write $\mathbb Z/M\mathbb Z$ for the ring of integers modulo $M$.

The **sites of the periodic lattice of side $M$** are the four-component arrays
over $\mathbb Z/M\mathbb Z$: the set of sites is

$$
\Lambda_M = (\mathbb Z/M\mathbb Z)^4 ,
$$

the set of all maps $x : \{0, 1, 2, 3\} \to \mathbb Z/M\mathbb Z$ from the
axes to the integers modulo $M$. The coordinate of the site $x$ on axis $i$ is
$x_i \in \mathbb Z/M\mathbb Z$. Sites are added and subtracted coordinatewise
modulo $M$, by the pointwise structure on maps:
$(x + y)_i = x_i + y_i$ and $(x - y)_i = x_i - y_i$ in
$\mathbb Z/M\mathbb Z$. No metric, ordering or embedding into $\mathbb Z^4$ is
part of the definition.

## Depends on

- [Axes and four-component arrays](axes-and-arrays.md)

## Sources

- [YM/Lattice ledger: Site](../../../sources/lattice-gauge-wilson.md#site)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
