# Lattice spacing and positions of sites

Let $C$ be a Wilson family for a matrix gauge group, with side lengths $L_p$
and denominators $m_N$, positive integers indexed by
$p, N \in \mathbb N = \{0, 1, 2, \dots\}$. The lattice with indices $N$ and
$p$ is the periodic lattice $\Lambda_M = (\mathbb Z/M\mathbb Z)^4$ of side
$M = L_p m_N$. Two quantities are defined from these data; neither is a
condition on the family.

The **lattice spacing** at the index $N \in \mathbb N$ is the real number

$$
a_N = \frac{1}{m_N}.
$$

The **position** of a site is defined for all $N, p \in \mathbb N$ as follows.
Put $M = L_p m_N$ and let $y \in \Lambda_M$ be a site, with coordinate
$y_j \in \mathbb Z/M\mathbb Z$ on each axis $j \in \{0, 1, 2, 3\}$. For each
$j$, let $\tilde y_j$ be the unique integer whose residue modulo $M$ is $y_j$
and which satisfies

$$
-\frac{M}{2} < \tilde y_j \le \frac{M}{2}.
$$

The position of $y$ is the point

$$
\mathrm{pos}_{N,p}(y) = \bigl(a_N \tilde y_0,\ a_N \tilde y_1,\ a_N \tilde y_2,\ a_N \tilde y_3\bigr) \in \mathbb R^4 .
$$

Thus the lattice axis $j$ is sent to the coordinate $j$ of $\mathbb R^4$, and
the lattice axis $3$ to the time coordinate, the last one. The integers
$\tilde y_j$ are centred at $0$ rather than taken from
$\{0, 1, \dots, M - 1\}$, and the interval is closed on the right: for even
$M$ the residue of $M/2$ is represented by $M/2$, not by $-M/2$. Since
$M a_N = L_p$, the condition on $\tilde y_j$ says equivalently that the
coordinate $a_N \tilde y_j$ lies in $(-L_p/2, L_p/2]$.

## Depends on

- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](wilson-family.md)
- [Periodic lattice](periodic-lattice.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [Declaration ledger of the Wilson lattice source: lattice spacing and positions](../../sources/public-wilson.md#lattice-spacing-and-positions)
