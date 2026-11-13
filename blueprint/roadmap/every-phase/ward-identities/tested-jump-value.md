# Tested value of the jump

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$. A joint test
function on $n$ points is a Schwartz function $(\mathbb R^4)^n \to \mathbb C$.

**Data.** Fix a Wilson family and let $S$ be a Euclidean correlation table
for its tokens, with quotient label spaces $F_d$ and common label space
$\mathbb F$; a graded label
is a pair $(d, \beta)$ with $\beta \in F_d$, and for a tuple $w$ of graded
labels $[w]$ is the tuple of the images $[\beta_i]_{d_i} \in \mathbb F$ of its
entries. Let $W$ be boundary distributions over $S$: for every $n$, a
complex-multilinear map $v \mapsto W_n(v)$ from $\mathbb F^n$ to tempered
distributions on $(\mathbb R^4)^n$. Fix

- a [Killing field](../stress-current/killing-field.md) $K$ with matrix $V$; for
  $y \in \mathbb R^4$, $K^b(y) = (K(y))_b$ is the component along the axis
  $b$ of its real value $K(y)$, the translation's component $b$ plus
  $\sum_c V_{bc} y_c$;
- rotations of $S$, with generator maps $\lambda_d$ from the skew-symmetric
  real $4 \times 4$ matrices to the complex-linear maps of $F_d$
  (real-linear in the matrix);
- derivative maps $\partial^{(d)}_b : F_d \to F_{d+1}$, complex linear, for
  every degree $d$ and axis $b$;
- spectator graded labels $v_0, \dots, v_{n-1}$, a slot
  $k \in \{0, \dots, n\}$ and a graded label $B = (d, \beta)$;
- a joint test function $M$ on $n+1$ points.

With $\theta = \mathrm{diag}(1, 1, 1, -1)$,
$A = \tfrac12(V - V^{\mathsf T})$, $C = V - A = \tfrac12(V + V^{\mathsf T})$
and $A' = \tfrac12\big(C\theta - (C\theta)^{\mathsf T}\big)$, the
infinitesimal label action of $K$ in degree $d$ is the complex-linear map
$\Sigma^{(d)}_K = \lambda_d(A) - \mathrm i\,\lambda_d(A') : F_d \to F_d$.
Let $\zeta_3 = -\mathrm i$ and $\zeta_b = 1$ for spatial $b$ be the Wick factors
of the [Minkowski stress labels](../stress-current/minkowski-stress-field.md). For an axis $b$,
$K^b_{(k)} M$ is the joint test function $x \mapsto K^b(x_k)\, M(x)$: the
[weighting](killing-weighted-tests.md) of $M$ by the component $b$ of $K$
through the linear map $x \mapsto x_k$ that reads the point in slot $k$.

**The value.** The **tested value of the jump** is the complex number

$$
\mathcal R_k(v, B; M) =
W_{n+1}\Big(\big[\operatorname{ins}_k\big(v;\ (d, \Sigma^{(d)}_K \beta)\big)\big]\Big)(M)
+ \sum_{b=0}^{3} \zeta_b\ W_{n+1}\Big(\big[\operatorname{ins}_k\big(v;\ (d+1, \partial^{(d)}_b \beta)\big)\big]\Big)\big(K^b_{(k)} M\big),
$$

the transformed label occupying slot $k$ and the spectators the other slots in
order ([insertion into a slot](../stress-current/slot-insertion.md)). No support condition on
$M$ is part of the definition.

## Depends on

- [Killing fields](../stress-current/killing-field.md)
- [Minkowski stress labels and the stress field](../stress-current/minkowski-stress-field.md)
- [Insertion into a slot](../stress-current/slot-insertion.md)
- [Test functions weighted by a Killing field](killing-weighted-tests.md)

## Sources

- [YM/EveryPhase ledger: Decree](../../../sources/every-phase.md#decree)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
