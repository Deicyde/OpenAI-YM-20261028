# All-orders separated operator product expansion

The third of the four properties the challenge asks of a continuum hierarchy
is an operator product expansion. The
[upstream description](../../sources/upstream-readme.md#all-orders-separated-ope)
states it in four sentences:

> For each finite cluster and collection of separated spectators, use a single
> system of coefficients at every truncation degree and in every phase. Both
> the full word and each term with the cluster replaced by a local insertion
> are reads of the same hierarchy. The bounds are uniform at all sufficiently
> small radii for the specified cluster size and separation constants.
> Permutation symmetry and smoothness hold off the collision diagonals.

This chapter states the expansion as the challenge formalizes it, which makes
the first three sentences precise. The fourth sentence is not part of the
expansion in the formal statement: the permutation symmetry and the smoothness
of the correlations at configurations of pairwise distinct points are two of
the [reconstruction conditions](../continuum-hierarchy/reconstruction.md).

The expansion is a condition on one
[continuum hierarchy](../continuum-hierarchy/hierarchy.md) $T$ over a
[Wilson family](../wilson-lattice/wilson-family.md) for a
[matrix gauge group](../gauge-groups/gauge-group.md). In the words of a
comment in the formal specification, "all correlation terms, including every
spectator in the OPE, are evaluations of one hierarchy". Of the data of $T$,
the expansion uses the following. For each grade
$d \in \mathbb N$ there is a finite-dimensional
complex normed space $F_d$ of fields of grade $d$, and a graded field is a
pair $(d, u)$ with $u \in F_d$. There is a set $X$ of characters, and for
every $n \in \mathbb N$, every $s$ that is a character or the extra value
"unselected", written $*$, every $n$-tuple $v$ of graded fields and every
configuration $z$ of $n$ points of $\mathbb R^4$, there is a correlation
$S_s(v; z) \in \mathbb C$. For each $j \in \mathbb N$ there is a finite set
$\mathrm{Ch}_j$ of channels, and each channel $\kappa \in \mathrm{Ch}_j$ has
an actor $A_j(\kappa) \in F_j$. Finally, for every family
$a = (a_i)_{i \in I}$ of graded fields indexed by a finite set $I$, every
$j \in \mathbb N$, every channel $\kappa \in \mathrm{Ch}_j$, every family
$x = (x_i)_{i \in I}$ of points of $\mathbb R^4$ and every centre
$o \in \mathbb R^4$, there is a coefficient
$C^{j,\kappa}_a(x; o) \in \mathbb C$. The expansion is a condition on these
data and adds none.

Positions are points of $\mathbb R^4$, and every distance is Euclidean, as in
the chapter on [spacetime](../spacetime/README.md); no Minkowski geometry
enters. For a scale $r$ and constants $M$ and $\eta$, a family of points
$x_i$, $i \in I$, is a cluster around a centre $o$ when every $x_i$ lies
within distance $M r$ of $o$ and points with different indices are at least
$\eta r$ apart. Spectators are points $y_m$, $m \in J$, at distance at least
$c$ from the centre and from one another; this condition refers to the centre,
not to the individual points of the cluster. The weight $w(a)$ of a family $a$
of graded fields is the sum of their grades. The joint correlation
$S_s(a@x;\, b@y)$ of graded fields $a_i$ at the points $x_i$ and $b_m$ at the
points $y_m$ is a single correlation of $T$: in the words of the comment on
its definition in the formal specification, "enumerate the union of the
insertion and spectator slots once, then read the hierarchy". The order in
which the slots are listed is fixed by the definition, through a choice it
does not specify.

The expansion consists of two families of bounds, required for all finite
index sets, all families of graded fields and all constants $M \ge 0$,
$\eta > 0$, $c > 0$ and $\varepsilon > 0$. The coefficients obey
$|C^{j,\kappa}_a(x; o)| \le r^{\,j - w(a) - \varepsilon}$ whenever $x$ is a
cluster at scale $r$ around $o$. And for every truncation degree
$D \in \mathbb N$, whenever in addition the spectators $y$ are clear of $o$,
the joint correlation $S_s(a@x;\, b@y)$ differs from the truncated sum

$$
\sum_{j=0}^{D} \sum_{\kappa \in \mathrm{Ch}_j}
C^{j,\kappa}_a(x; o)\, S_s\big((j, A_j(\kappa))@o;\, b@y\big)
$$

by at most $r^{\,D + 1 - w(a) - \varepsilon}$. Each term of the sum replaces
the cluster by the single graded field $(j, A_j(\kappa))$ placed at the
centre, the description's "local insertion", and keeps the same spectators and
the same $s$; the full correlation and each replaced term are joint
correlations of the one hierarchy $T$. Both bounds hold for all sufficiently
small $r > 0$: below a threshold that may depend on everything fixed before
$r$, namely the index sets, the graded fields, the constants, and the degree
$D$ in the remainder bounds or $j$ and $\kappa$ in the coefficient bounds, but
not on the positions or on $s$. The coefficients are those of $T$, the same
for every truncation degree, every family of spectators and every $s$, a
character or unselected; this is the description's "single system of
coefficients at every truncation degree and in every phase". The remainder
bounds are required at every truncation degree $D$, which is the sense in
which the expansion holds to all orders.

## Clusters and spectators

The cluster and clearance conditions concern real numbers and points of
$\mathbb R^4$ alone, and put no sign condition on the scale or the constants;
the expansion supplies those. The weight and the joint correlation are read
from the hierarchy.

- [Clusters and clear spectators](clusters-and-spectators.md)
- [Weight of a cluster](cluster-weight.md)
- [Joint correlation of a cluster and spectators](grouped-correlation.md)

## The expansion

The operator product expansion is the pair of conditions formed by the
coefficient bounds and the remainder bounds. It is the third of the
[four properties of a hierarchy](../challenge/hierarchy-properties.md).

- [Operator product expansion](operator-product-expansion.md)
