# The current jump at Euclidean points

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$; for
$y \in \mathbb R^4$, $t(y) = y_3$ and $\vec y$ is its spatial part. Fix a
Wilson family and let $S$ be a Euclidean correlation table for its tokens,
with quotient label spaces $F_d$ and common label space $\mathbb F$; a graded label is a pair
$(d, \beta)$ with $\beta \in F_d$, and $[w]$ is the tuple of images in
$\mathbb F$ of a tuple $w$ of graded labels.

**Hypotheses.** Let a second correlation table $U$, for the same tokens as
$S$, inclusion and derivative maps $\rho_{d,e}$ and $\partial^{(d)}_a$ for
$S$, the symmetry and reality conditions for $S$, a
stress tensor $T = (T_{ab})$ of $S$, boundary distributions $W$ with cutoff
functions $\chi_n$, a continuation $\mathsf F$ and a Laplace family $Z$ for $W$ satisfy
the [hypotheses for continuing the stress current](stress-continuation-hypotheses.md).
Let rotations of $S$ be given: for every degree $d$, an invertible
complex-linear map of $F_d$ for each orthogonal $4 \times 4$ matrix, and a
real-linear map $\lambda_d$ from the skew-symmetric real $4 \times 4$
matrices to the complex-linear maps of $F_d$,
and assume the **Euclidean Ward identities** of $U$, $T$, the maps
$\partial^{(d)}_b$ and the maps $\lambda_d$: for every $m \in \mathbb N$, every
separated configuration $x = (x_0, \dots, x_m)$ of $m + 1$ points (its points
pairwise distinct), all graded
labels $q_1, \dots, q_m$, every smooth compactly supported function
$\varpi : \mathbb R^4 \to \mathbb R$ equal to $1$ on a neighbourhood of $x_0$
whose closed support contains none of $x_1, \dots, x_m$, every degree $d$ and
every $\beta \in F_d$,

$$
-\sum_{a=0}^{3} \int_{\mathbb R^4} \partial_a\varpi(y)\ U\big((y, x);\ (4, T_{ab}), (d, \beta), q\big)\, dy
= U\big(x;\ (d+1, \partial^{(d)}_b\beta), q\big)
$$

for every axis $b$, and

$$
-\sum_{a=0}^{3}\sum_{b=0}^{3} \int_{\mathbb R^4} \partial_a\varpi(y)\, \big(\Xi(y - x_0)\big)_b\ U\big((y, x);\ (4, T_{ab}), (d, \beta), q\big)\, dy
= U\big(x;\ (d, \lambda_d(\Xi)\beta), q\big)
$$

for every skew-symmetric real $4 \times 4$ matrix $\Xi$. Here $(y, x)$ is the
configuration $(y, x_0, \dots, x_m)$ of $m + 2$ points, carrying the labels
$(4, T_{ab})$ at $y$, $(d, \beta)$ at $x_0$ and $q_i$ at $x_i$; $U(x; w)$ is
the value of $U$ on fixed representatives of the classes; and the integrals
are Lebesgue integrals, taken to be $0$ when the integrand is not integrable.

**Statement.** Let $K$ be a [Killing field](killing-field.md), $n \in \mathbb N$,
$v_0, \dots, v_{n-1}$ spectator graded labels, $B$ a graded label, and
$x = (x_0, \dots, x_n) \in (\mathbb R^4)^{n+1}$ a configuration whose times
strictly increase,

$$
t(x_0) < t(x_1) < \dots < t(x_n).
$$

Let $k \in \{0, \dots, n\}$, and let $g$ be a Schwartz function on
$\mathbb R^3$ with compact support, real values, and $g = 1$ on a
neighbourhood of $\vec x_k$. Let $J_k$ be the
[current jump](integrated-current-jump.md) at slot $k$ of $Z$, $K$, $T$, the
labels $[\operatorname{ins}_k(v; B)] \in \mathbb F^{n+1}$ (the label $B$ in
slot $k$, see [insertion into a slot](slot-insertion.md)) and the spatial
test $g$, and let $p_{\mathrm E}(x)$ be the purely Euclidean base point of
$x$. Then

$$
\lim_{s \to 0^+} J_k\big(p_{\mathrm E}(x), s\big) = E,
$$

where $E$ is the [Euclidean value of the current jump](euclidean-jump-value.md)
of $U$, $K$, the rotations, the derivative maps, $v$, $x$, $k$ and $B$. The
limit is taken as $s$ tends to $0$ through positive values.

At the purely Euclidean base point the stress is inserted at the complex time
$\mathrm i\,(t(x_k) + s)$ just after the point $x_k$ and at
$\mathrm i\,(t(x_k) - s)$ just before it, the other points sitting at their
imaginary times $\mathrm i\, t(x_i)$, $i \ne k$.

## Depends on

- [Killing fields](killing-field.md)
- [Insertion into a slot](slot-insertion.md)
- [Hypotheses for continuing the stress current](stress-continuation-hypotheses.md)
- [Spatially integrated current and its jump](integrated-current-jump.md)
- [Euclidean value of the current jump](euclidean-jump-value.md)

## Sources

- [YM/EveryPhase ledger: Pure](../../sources/every-phase.md#pure)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
