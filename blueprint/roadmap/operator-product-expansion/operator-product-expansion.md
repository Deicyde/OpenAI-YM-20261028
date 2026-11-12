# Operator product expansion

Let $T$ be a continuum hierarchy over a Wilson family for a matrix gauge
group. The operator product expansion is a condition on $T$, made of the two
conditions below; it adds no data. It uses the following parts of the data of
$T$, where $\mathbb N = \{0, 1, 2, \dots\}$:

- for each grade $d \in \mathbb N$, the finite-dimensional complex normed space
  $F_d$ of fields of grade $d$; a graded field is a pair $(d, u)$ with
  $d \in \mathbb N$ and $u \in F_d$;
- the set $X$ of characters; below, $s$ always stands for either a character
  (an element of $X$) or the extra value "unselected", written $*$;
- the correlations: a complex number $S_s(v; z)$ for every $n \in \mathbb N$,
  every $s$, every $n$-tuple $v$ of graded fields and every configuration $z$
  of $n$ points of $\mathbb R^4$;
- for each $j \in \mathbb N$, the finite set $\mathrm{Ch}_j$ of channels and,
  for each channel $\kappa \in \mathrm{Ch}_j$, the actor
  $A_j(\kappa) \in F_j$, so that $(j, A_j(\kappa))$ is a graded field;
- the coefficients: a complex number $C^{j,\kappa}_a(x; o)$ for every finite
  set $I$, every family $a = (a_i)_{i \in I}$ of graded fields, every
  $j \in \mathbb N$, every $\kappa \in \mathrm{Ch}_j$, every family
  $x = (x_i)_{i \in I}$ of points of $\mathbb R^4$ and every point
  $o \in \mathbb R^4$.

The conditions use four notions built from these, with the Euclidean distance
$\|q - q'\|$ between points $q, q'$ of $\mathbb R^4$. For a finite set $I$ and
a family $a = (a_i)_{i \in I}$ of graded fields with $a_i = (d_i, u_i)$, the
weight of $a$ is the real number $w(a) = \sum_{i \in I} d_i$. For real numbers
$r$, $M$ and $\eta$, a family $x = (x_i)_{i \in I}$ of points and a point $o$,
the family $x$ is an $(r, M, \eta)$-cluster around $o$ when
$\|x_i - o\| \le M r$ for every $i \in I$ and $\eta r \le \|x_i - x_{i'}\|$ for
all $i, i' \in I$ with $i \ne i'$. For a point $o$, a family
$y = (y_m)_{m \in J}$ of points and a real number $c$, the family $y$ is
$c$-clear of $o$ when $c \le \|o - y_m\|$ for every $m \in J$ and
$c \le \|y_m - y_{m'}\|$ for all $m, m' \in J$ with $m \ne m'$. For finite sets
$I$ and $J$, families $a = (a_i)_{i \in I}$ and $b = (b_m)_{m \in J}$ of graded
fields, families $x = (x_i)_{i \in I}$ and $y = (y_m)_{m \in J}$ of points and
an $s$, the joint correlation $S_s(a@x;\, b@y)$ is the correlation $S_s$ read
at the $|I| + |J|$ graded fields $a_i$ at the points $x_i$ and $b_m$ at the
points $y_m$, listed in the order of the listing of the disjoint union
$I \sqcup J$ that its definition fixes.

Finally, $|\cdot|$ is the modulus of a complex number; for $r > 0$ and a real
number $\alpha$, $r^\alpha = e^{\alpha \ln r}$; and a statement holds *for all
sufficiently small $r > 0$* when there is a real number $r_0 > 0$ such that it
holds for every real number $r$ with $0 < r < r_0$.

The hierarchy $T$ **satisfies the operator product expansion** when the
following two conditions hold.

**1. Coefficient bounds.** For every finite set $I$, every family
$a = (a_i)_{i \in I}$ of graded fields, all real numbers $M$, $\eta$ and
$\varepsilon$ with $M \ge 0$, $\eta > 0$ and $\varepsilon > 0$, every
$j \in \mathbb N$ and every channel $\kappa \in \mathrm{Ch}_j$, the following
holds for all sufficiently small $r > 0$: for every family
$x = (x_i)_{i \in I}$ of points of $\mathbb R^4$ and every point
$o \in \mathbb R^4$ such that $x$ is an $(r, M, \eta)$-cluster around $o$,

$$
\big| C^{j,\kappa}_a(x; o) \big| \le r^{\,j - w(a) - \varepsilon}.
$$

**2. Remainder bounds.** For all finite sets $I$ and $J$, all families
$a = (a_i)_{i \in I}$ and $b = (b_m)_{m \in J}$ of graded fields, all real
numbers $M$, $\eta$, $c$ and $\varepsilon$ with $M \ge 0$, $\eta > 0$, $c > 0$
and $\varepsilon > 0$, and every $D \in \mathbb N$, the following holds for
all sufficiently small $r > 0$: for every family $x = (x_i)_{i \in I}$ of
points of $\mathbb R^4$, every point $o \in \mathbb R^4$ and every family
$y = (y_m)_{m \in J}$ of points of $\mathbb R^4$ such that $x$ is an
$(r, M, \eta)$-cluster around $o$ and $y$ is $c$-clear of $o$, and for every
$s$,

$$
\Big| S_s(a@x;\, b@y)
- \sum_{j=0}^{D} \sum_{\kappa \in \mathrm{Ch}_j}
C^{j,\kappa}_a(x; o)\, S_s\big((j, A_j(\kappa))@o;\, b@y\big) \Big|
\le r^{\,D + 1 - w(a) - \varepsilon}.
$$

Here $S_s\big((j, A_j(\kappa))@o;\, b@y\big)$ is the joint correlation, for
the same $s$, of the family indexed by one fixed one-element set $\{\star\}$,
the same set in every term of the sum, whose single graded field
$(j, A_j(\kappa))$ is placed at the centre $o$, together with the same graded
fields $b$ at the same points $y$; its slots are listed by the one listing of
$\{\star\} \sqcup J$ that the definition of the joint correlation fixes.

In the coefficient bounds the threshold $r_0$ may depend on $I$, $a$, $M$,
$\eta$, $\varepsilon$, $j$ and $\kappa$, and one threshold serves all $x$ and
$o$. In the remainder bounds it may depend on $I$, $J$, $a$, $b$, $M$, $\eta$,
$c$, $\varepsilon$ and $D$, and one threshold serves all $x$, $o$, $y$ and
$s$. Neither bound carries a multiplicative constant. The coefficients
$C^{j,\kappa}_a(x; o)$ are data of $T$ and do not depend on $D$, on the
spectators $b$ at $y$ or on $s$: the same coefficients enter the remainder
bounds for every $D$, every family $b$ at $y$ and every $s$.

## Depends on

- [Continuum hierarchy](../continuum-hierarchy/hierarchy.md)
- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](../wilson-lattice/wilson-family.md)
- [Clusters and clear spectators](clusters-and-spectators.md)
- [Weight of a cluster](cluster-weight.md)
- [Joint correlation of a cluster and spectators](grouped-correlation.md)

## Sources

- [ChallengeSpec.lean ledger: operator product expansion](../../sources/challenge-spec.md#operator-product-expansion)
- [Upstream description: all-orders separated OPE](../../sources/upstream-readme.md#all-orders-separated-ope)
