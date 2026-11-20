# Separation of two sites

Fix a side $M$, a positive integer, and write $\tilde z \in \mathbb Z^4$ for the
centred lift of a site $z \in \Lambda_M$.

The **torus modulus** of a site $z \in \Lambda_M$ is the largest absolute value
of a coordinate of its centred lift:

$$
|z|_M = \max_{i \in \{0, 1, 2, 3\}} |\tilde z_i| ,
$$

a natural number. The **separation** of two sites $x, y \in \Lambda_M$ is the
torus modulus of their difference,

$$
|x - y|_M ,
$$

where $x - y \in \Lambda_M$ is the coordinatewise difference modulo $M$. The
centred lift is applied to the difference $x - y$, not to $x$ and $y$
separately. The separation is a natural number, defined for every side $M$ and
every pair of sites, $x = y$ included.

## Depends on

- [Centred lift of a site](centred-lift.md)

## Sources

- [YM/Lattice ledger: Site](../../../sources/lattice-gauge-wilson.md#site)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
