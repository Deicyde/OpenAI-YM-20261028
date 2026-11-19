# Minkowski jump identity

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$. A joint test
function on $n$ points is a Schwartz function $(\mathbb R^4)^n \to \mathbb C$;
the support $\operatorname{supp} h$ of a function $h$ is the closure of the set
where it is not zero. A configuration of $N$ points is separated when its
points are pairwise distinct.

**Data.** Fix a Wilson family and data for the
[hypotheses for continuing the stress current](../stress-current/stress-continuation-hypotheses.md):
a Euclidean correlation table $S$ for its tokens, with quotient label spaces
$F_d$, common label space $\mathbb F$ and images $[\beta]_d \in \mathbb F$ of
$\beta \in F_d$; a second correlation table $U$, with values $U(x; w)$ at
configurations $x$ on graded labels $w$ of $S$; inclusion and derivative maps
$\rho_{d,e}$ and $\partial^{(d)}_a : F_d \to F_{d+1}$; the reflection and
reality hypothesis on $S$; a stress tensor $T = (T_{ab})$ of $S$; boundary
distributions $W$ over $S$ with cutoffs $\chi_n$; a continuation $\mathsf F$; and a
Laplace family $Z$ for $W$. Fix moreover

- rotations of $S$, with generator maps $\lambda_d$ from the skew-symmetric
  real $4 \times 4$ matrices to the complex-linear maps of $F_d$;
- a [Killing field](../stress-current/killing-field.md) $K$;
- spectator graded labels $v_0, \dots, v_{n-1}$, a slot
  $k \in \{0, \dots, n\}$ and a graded label $B = (d, \beta)$;
- a joint test function $M$ on $n+1$ points, a Schwartz function
  $g \in \mathcal S(\mathbb R^3)$ of space and a Schwartz function
  $f \in \mathcal S(\mathbb R)$ of time.

**Stress laws.** A window for a separated configuration
$x = (x_0, \dots, x_N)$ of $N+1$ points is an infinitely differentiable,
compactly supported function $\varpi : \mathbb R^4 \to \mathbb R$ that equals
$1$ on a neighbourhood of $x_0$ and whose support contains none of the points
$x_1, \dots, x_N$. The stress $T$ satisfies the **stress laws** in $U$, for the
derivative maps and the generator maps, when for every $N$, every separated
configuration $x$ of $N+1$ points, all graded labels
$q = (q_0, \dots, q_{N-1})$, every window $\varpi$ for $x$, every degree $e$
and every $\beta' \in F_e$:

- *translation law:* for every axis $b$,

    $$
    -\sum_{a=0}^{3} \int_{\mathbb R^4} \partial_a \varpi(y)\ U\big((y, x_0, \dots, x_N);\ (4, T_{ab}), (e, \beta'), q\big)\, dy
    = U\big(x;\ (e+1, \partial^{(e)}_b \beta'), q\big);
    $$

- *rotation law:* for every skew-symmetric real $4 \times 4$ matrix $\Xi$,

    $$
    -\sum_{a=0}^{3}\sum_{b=0}^{3} \int_{\mathbb R^4} \partial_a \varpi(y)\, \big(\Xi (y - x_0)\big)_b\ U\big((y, x_0, \dots, x_N);\ (4, T_{ab}), (e, \beta'), q\big)\, dy
    = U\big(x;\ (e, \lambda_e(\Xi)\beta'), q\big).
    $$

Here $\partial_a \varpi$ is the derivative of $\varpi$ along the $a$-th
standard basis vector, the labels $q$ follow the displayed ones in order, and
the integrals are Lebesgue integrals, taken to be $0$ when the integrand is not
integrable.

**Statement.** Assume:

1. the data satisfy the hypotheses for continuing the stress current;
2. $T$ satisfies the stress laws in $U$ for the derivative maps and the
   generator maps;
3. $M$ has compact support;
4. $g$ has compact support and real values: $g(r) \in \mathbb R$ for every
   $r \in \mathbb R^3$;
5. $f$ has compact support;
6. $W$ and $Z$ have
   [exchange heights for every adjacent pair](exchange-height-sequences.md);
7. for every $x \in \operatorname{supp} M$, the cutoff $g$ and the profile $f$
   satisfy the [spacelike condition](spacelike-cutoff-condition.md) at the
   point $x_k$ of $x$ in slot $k$.

Let $\alpha = \big[\operatorname{ins}_k(v; B)\big] \in \mathbb F^{n+1}$ be the
labels with $[\beta]_d$ in slot $k$ and the images $[v_i]$ of the spectators in
the other slots ([insertion into a slot](../stress-current/slot-insertion.md)). Then

$$
\mathcal J_{k+1}(\alpha; M, g, f) - \mathcal J_k(\alpha; M, g, f) = \mathcal R_k(v, B; M)\ \int_{\mathbb R} f(\tau)\, d\tau ,
$$

where $\mathcal J_j$ is the
[tested stress insertion](tested-current-jump.md) in slot $j$ of $\alpha$ (slot
$k+1$ places the stress immediately after the field of $B$, slot $k$
immediately before it), built from $W$, $K$ and $T$, and $\mathcal R_k$ is the
[tested value of the jump](tested-jump-value.md), built from $W$, $K$, the
generator maps $\lambda_d$ and the derivative maps $\partial^{(d)}_b$.

## Depends on

- [Killing fields](../stress-current/killing-field.md)
- [Insertion into a slot](../stress-current/slot-insertion.md)
- [Hypotheses for continuing the stress current](../stress-current/stress-continuation-hypotheses.md)
- [Exchange heights for every adjacent pair](exchange-height-sequences.md)
- [Spacelike condition on cutoff and profile](spacelike-cutoff-condition.md)
- [Tested stress insertion next to a field](tested-current-jump.md)
- [Tested value of the jump](tested-jump-value.md)

## Proof depends on

- [Joint limit of the current jump](../stress-current/joint-current-jump-limit.md)
- [Continued value of the current jump](../stress-current/continued-jump-value.md)
- [Spatially integrated current and its jump](../stress-current/integrated-current-jump.md)
- [Admissible base points for the current jump](../stress-current/jump-admissibility.md)
- [Test functions weighted by a Killing field](killing-weighted-tests.md)
- [Minkowski stress labels and the stress field](../stress-current/minkowski-stress-field.md)

## Sources

- [YM/EveryPhase ledger: Decree](../../../../sources/every-phase.md#decree)
- [Armstrong's informalization: unit V.3](../../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
