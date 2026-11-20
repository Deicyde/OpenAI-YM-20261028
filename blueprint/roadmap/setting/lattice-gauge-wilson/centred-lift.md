# Centred lift of a site

The **cover** is the set $\mathbb Z^4$ of four-component arrays of integers.

Fix a side $M$, a positive integer. For a site $x \in \Lambda_M$ and an axis
$i$, let $w_i \in \{0, 1, \dots, M - 1\}$ be the standard representative of the
coordinate $x_i \in \mathbb Z/M\mathbb Z$. The **centred lift** of $x$ is the
integer array $\tilde x \in \mathbb Z^4$ with coordinates

$$
\tilde x_i =
\begin{cases}
w_i, & w_i \le \lfloor M/2 \rfloor, \\
w_i - M, & w_i > \lfloor M/2 \rfloor,
\end{cases}
\qquad i = 0, 1, 2, 3 .
$$

The lift is taken coordinate by coordinate: a coordinate keeps its standard
representative $w_i$ when $w_i \le \lfloor M/2 \rfloor$ and is shifted down by
$M$ otherwise. In particular, when $M$ is even, the representative $w_i = M/2$
is kept, and $\tilde x_i = M/2$.

## Depends on

- [Sites of the periodic lattice](torus-sites.md)

## Sources

- [YM/Lattice ledger: Site](../../../sources/lattice-gauge-wilson.md#site)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
