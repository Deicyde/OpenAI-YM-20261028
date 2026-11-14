# Joint limit of the current jump

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$. Fix a Wilson
family and let $S$ be a Euclidean correlation table for its tokens, with
quotient label spaces $F_d$ and common label space $\mathbb F$; a graded label is a pair
$(d, \beta)$ with $\beta \in F_d$, and $[w]$ is the tuple of images in
$\mathbb F$ of a tuple $w$ of graded labels.

**Hypotheses.** Let a second correlation table $U$, for the same tokens as
$S$, inclusion and derivative maps $\rho_{d,e}$ and $\partial^{(d)}_a$ for
$S$, the symmetry and reality conditions for $S$, a
stress tensor $T$ of $S$, boundary distributions $W$ with cutoff functions
$\chi_n$, a continuation $\mathsf F$ and a Laplace family $Z$ for $W$ satisfy the
[hypotheses for continuing the stress current](stress-continuation-hypotheses.md).
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
$v_0, \dots, v_{n-1}$ spectator graded labels, $k \in \{0, \dots, n\}$ a slot
and $B$ a graded label. Let $g$ be a Schwartz function on $\mathbb R^3$ with
compact support and real values. Let $p = (\xi, u, t)$ be a
[base point](integrated-current-jump.md) for $n + 1$ points, with
$\xi \in (\mathbb R^3)^{n+1}$, $u \in \mathbb C^{n+1}$ and $t \in \mathbb R$,
such that

1. $g = 1$ on a neighbourhood of $\xi_k$;
2. the complex times of $p$ have strictly increasing imaginary parts,
   $\operatorname{Im} u_0 < \operatorname{Im} u_1 < \dots < \operatorname{Im} u_n$;
3. $p$ [allows](jump-admissibility.md) $g$ at the slot $k$:
   $|t| < \|r - \xi_k\|$ for every spatial axis $i$ and every $r$ in the closed
   support of $\partial_i g$; and
4. $Z$ has [exchange data](jump-admissibility.md) at the tied heights
   $\eta(p, k) \in \mathbb R^{n+2}$ of $p$ for the slot $k$.

Let $J_k$ be the [current jump](integrated-current-jump.md) at slot $k$ of
$Z$, $K$, $T$, the labels $[\operatorname{ins}_k(v; B)] \in \mathbb F^{n+1}$
(the label $B$ in slot $k$, see [insertion into a slot](slot-insertion.md))
and the spatial test $g$. Then

$$
\lim_{(p', s) \to (p, 0^+)} J_k(p', s) = C,
$$

where $C$ is the [continued value of the current jump](continued-jump-value.md)
of $Z$, $K$, the rotations, the derivative maps, $v$, $k$ and $B$ at the pair
$(\xi, u)$ of spatial positions and complex times of $p$. The limit is joint: for
every $\varepsilon > 0$ there are a neighbourhood $N$ of $p$ in the space of
base points for $n + 1$ points and a $\delta > 0$ such that
$|J_k(p', s) - C| < \varepsilon$ for every base point $p' \in N$ and every
$s$ with $0 < s < \delta$.

## Depends on

- [Killing fields](killing-field.md)
- [Insertion into a slot](slot-insertion.md)
- [Hypotheses for continuing the stress current](stress-continuation-hypotheses.md)
- [Spatially integrated current and its jump](integrated-current-jump.md)
- [Admissible base points for the current jump](jump-admissibility.md)
- [Continued value of the current jump](continued-jump-value.md)

## Proof depends on

- [The current jump at Euclidean points](euclidean-current-jump.md)
- [Euclidean value of the current jump](euclidean-jump-value.md)
- [Minkowski stress labels and the stress field](minkowski-stress-field.md)
- [Tested stress insertion next to a field](../ward-identities/tested-current-jump.md)

## Sources

- [YM/EveryPhase ledger: Through](../../../sources/every-phase.md#through)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
