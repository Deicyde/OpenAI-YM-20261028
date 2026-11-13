# Ward identity with arbitrary spectators

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$. The support
$\operatorname{supp} h$ of a function $h$ is the closure of the set where it is
not zero. A configuration of $N$ points is separated when its points are
pairwise distinct.

**Data.** Fix a Wilson family and data for the
[hypotheses for continuing the stress current](stress-continuation-hypotheses.md):
a Euclidean correlation table $S$ for its tokens, with quotient label spaces
$F_d$ and common label space $\mathbb F$; a second correlation table $U$, with
values $U(x; w)$ at configurations $x$ on graded labels $w$ of $S$; inclusion
and derivative maps $\rho_{d,e}$ and $\partial^{(d)}_a : F_d \to F_{d+1}$; the
reflection and reality hypothesis on $S$; a stress tensor $T = (T_{ab})$ of
$S$; boundary distributions $W$ over $S$ with cutoffs $\chi_n$; a continuation
$\mathsf F$; and a Laplace family $Z$ for $W$. Fix moreover rotations of $S$, with
generator maps $\lambda_d$ from the skew-symmetric real $4 \times 4$ matrices
to the complex-linear maps of $F_d$; a [Killing field](killing-field.md) $K$;
a graded label $B = (d, \beta)$; a Schwartz function
$m \in \mathcal S(\mathbb R^4)$; a Schwartz function
$g \in \mathcal S(\mathbb R^3)$ of space; and a Schwartz function
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
3. $W$ and $Z$ have
   [exchange heights for every adjacent pair](exchange-height-sequences.md);
4. $m$ has compact support;
5. $g$ has compact support and real values: $g(r) \in \mathbb R$ for every
   $r \in \mathbb R^3$;
6. $f$ has compact support and $\int_{\mathbb R} f(\tau)\, d\tau = 1$;
7. for every $x \in \operatorname{supp} m$, the cutoff $g$ and the profile $f$
   satisfy the [spacelike condition](spacelike-cutoff-condition.md) at $x$.

Then for all words $a$ and $b$, whose letters carry arbitrary Schwartz test
functions, the [shell identity](shell-identity.md) for $W$, the generator maps
$\lambda_d$, the derivative maps $\partial^{(d)}_i$, $T$, $K$, $f$, $g$, $B$
and $m$ holds for $a$ and $b$:

$$
\sum_{i=0}^{3} \zeta_i\, \mathcal E\big(a\, \ell\, r_i\, b\big) - \sum_{i=0}^{3} \zeta_i\, \mathcal E\big(a\, r_i\, \ell\, b\big)
= \mathcal E\Big(a\, \big([\Sigma^{(d)}_K \beta]_d,\ m\big)\, b\Big)
+ \sum_{i=0}^{3} \zeta_i\, \mathcal E\Big(a\, \big([\partial^{(d)}_i \beta]_{d+1},\ K^i m\big)\, b\Big),
$$

with $\ell = ([\beta]_d, m)$, $r_i = ([T_{3i}]_4, K^i(g \otimes f))$, the Wick
factors $\zeta_i$, the infinitesimal label action $\Sigma^{(d)}_K$ and the
word expectations $\mathcal E$ under $W$ as in the shell identity.

## Depends on

- [Killing fields](killing-field.md)
- [Hypotheses for continuing the stress current](stress-continuation-hypotheses.md)
- [Exchange heights for every adjacent pair](exchange-height-sequences.md)
- [Spacelike condition on cutoff and profile](spacelike-cutoff-condition.md)
- [Shell identity for word expectations](shell-identity.md)

## Proof depends on

- [Minkowski jump identity](minkowski-jump-identity.md)
- [Insertion into a slot](slot-insertion.md)
- [Tested stress insertion next to a field](tested-current-jump.md)
- [Tested value of the jump](tested-jump-value.md)
- [Test functions weighted by a Killing field](killing-weighted-tests.md)
- [Minkowski stress labels and the stress field](minkowski-stress-field.md)

## Sources

- [YM/EveryPhase ledger: Court](../../sources/every-phase.md#court)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
