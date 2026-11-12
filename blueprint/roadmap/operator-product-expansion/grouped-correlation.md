# Joint correlation of a cluster and spectators

Let $T$ be a continuum hierarchy over a Wilson family for a matrix gauge
group. The definition uses three parts of the data of $T$. For each grade
$d \in \mathbb N$, where $\mathbb N = \{0, 1, 2, \dots\}$, there is the
finite-dimensional complex normed space $F_d$ of fields of grade $d$, and a
graded field is a pair $(d, u)$ with $d \in \mathbb N$ and $u \in F_d$. There
is the set $X$ of characters of $T$. And for every $n \in \mathbb N$, every
$s$ that is either a character (an element of $X$) or the extra value
"unselected", written $*$, every $n$-tuple $v = (v_0, \dots, v_{n-1})$ of
graded fields and every configuration $z = (z_0, \dots, z_{n-1})$ of $n$
points of $\mathbb R^4$, there is the correlation $S_s(v; z)$, a complex
number defined at every configuration of $n$ points, coincident points
included.

Let $I$ and $J$ be finite sets. Their disjoint union $I \sqcup J$ has one
element for each element of $I$ and one for each element of $J$, the two kinds
kept apart even where $I$ and $J$ share elements; call its elements slots, the
slot of $i \in I$ and the slot of $m \in J$. Let $n$ be the number of slots,
so that $n = |I| + |J|$. For this pair of sets the definition fixes one
bijection

$$
\ell : \{0, 1, \dots, n-1\} \to I \sqcup J,
$$

a listing of the slots chosen once and for all; which bijection is chosen is
not specified.

Let $s$ be a character or $*$, let $a = (a_i)_{i \in I}$ be a family of graded
fields with positions $x = (x_i)_{i \in I}$ in $\mathbb R^4$, and let
$b = (b_m)_{m \in J}$ be a family of graded fields with positions
$y = (y_m)_{m \in J}$ in $\mathbb R^4$. For $k = 0, 1, \dots, n-1$, set
$(v_k, z_k) = (a_i, x_i)$ when $\ell(k)$ is the slot of $i \in I$, and
$(v_k, z_k) = (b_m, y_m)$ when $\ell(k)$ is the slot of $m \in J$. The
**joint correlation** of the graded fields $a$ at $x$ and $b$ at $y$, for $s$,
is the complex number

$$
S_s(a@x;\, b@y) = S_s\big((v_0, \dots, v_{n-1});\, (z_0, \dots, z_{n-1})\big).
$$

So the slots of $I$ and of $J$ are listed once, in the order that $\ell$
fixes, and the correlation $S_s$ of $T$ is read at the graded fields and
positions in that order. No condition is placed on the positions: the joint
correlation is defined for all families $x$ and $y$, coincident points
included, whether or not $x$ is a cluster or $y$ is clear of any point.

## Depends on

- [Continuum hierarchy](../continuum-hierarchy/hierarchy.md)
- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](../wilson-lattice/wilson-family.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [ChallengeSpec.lean ledger: grouped correlation](../../sources/challenge-spec.md#grouped-correlation)
- [Upstream description: all-orders separated OPE](../../sources/upstream-readme.md#all-orders-separated-ope)
