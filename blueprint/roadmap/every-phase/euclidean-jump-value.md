# Euclidean value of the current jump

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$; for
$y \in \mathbb R^4$, $t(y) = y_3$ and $\vec y$ is its spatial part. Fix a
Wilson family and let $S$ be a Euclidean correlation table for its tokens,
with quotient label spaces $F_d$; a graded label is a pair $(d, \beta)$ with
$\beta \in F_d$. Let $U$ be a second correlation table, for the same tokens
as $S$; for a configuration $x$ of $m$ points and graded labels
$w_0, \dots, w_{m-1}$, $U(x; w)$ is the value of $U$ at $x$ on fixed
representatives of the classes $w_i$.

**Data.** Fix

- a [Killing field](killing-field.md) $K$, with matrix part $V$ and
  Euclidean columns $K^b_{\mathrm E}$;
- rotations of $S$: for every degree $d$, a map assigning to each orthogonal
  $4 \times 4$ matrix a complex-linear automorphism of $F_d$ (no group laws
  are assumed, and these maps are not used below), and a real-linear map
  $\lambda_d$ from the skew-symmetric real $4 \times 4$ matrices to the
  complex-linear maps of $F_d$;
- derivative maps $\partial^{(d)}_b : F_d \to F_{d+1}$ for every degree $d$
  and axis $b$, complex linear (part of a system of inclusion and derivative
  maps for $S$);
- spectator graded labels $v_0, \dots, v_{n-1}$, a configuration
  $x = (x_0, \dots, x_n) \in (\mathbb R^4)^{n+1}$, a slot
  $k \in \{0, \dots, n\}$ and a graded label $B = (d, \beta)$.

**Label action of $K$.** Let $\theta = \mathrm{diag}(1, 1, 1, -1)$,
$A = \tfrac12 (V - V^{\mathsf T})$ the skew part of $V$, and
$A' = \tfrac12\big((V - A)\theta - ((V - A)\theta)^{\mathsf T}\big)$. The infinitesimal
label action of $K$ in degree $d$ is the complex-linear map

$$
\Sigma^{(d)}_K = \lambda_d(A) - \mathrm i\, \lambda_d(A') : F_d \to F_d .
$$

**The value.** The **Euclidean value of the current jump** is

$$
E = U\Big(x;\ \operatorname{ins}_k\big(v;\ (d, \Sigma^{(d)}_K\beta)\big)\Big)
+ \sum_{b=0}^{3} K^b_{\mathrm E}(x_k)\ U\Big(x;\ \operatorname{ins}_k\big(v;\ (d+1, \partial^{(d)}_b\beta)\big)\Big),
$$

the transformed label occupying slot $k$, at the point $x_k$, and the
spectators $v_0, \dots, v_{n-1}$ occupying the other slots in order
([insertion into a slot](slot-insertion.md)).

**Purely Euclidean base point.** For a configuration
$x = (x_0, \dots, x_{m-1}) \in (\mathbb R^4)^m$, the purely Euclidean
[base point](integrated-current-jump.md) of $x$ is

$$
p_{\mathrm E}(x) = \Big( (\vec x_0, \dots, \vec x_{m-1}),\ \big(\mathrm i\, t(x_0), \dots, \mathrm i\, t(x_{m-1})\big),\ 0 \Big),
$$

with the spatial parts of $x$ as spatial positions, the imaginary times
$\mathrm i\, t(x_i)$ as complex times, and shift $0$.

## Depends on

- [Killing fields](killing-field.md)
- [Insertion into a slot](slot-insertion.md)
- [Spatially integrated current and its jump](integrated-current-jump.md)

## Sources

- [YM/EveryPhase ledger: Shell](../../sources/every-phase.md#shell)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
