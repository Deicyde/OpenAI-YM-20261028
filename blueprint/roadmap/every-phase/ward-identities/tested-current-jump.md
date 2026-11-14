# Tested stress insertion next to a field

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$; for
$y \in \mathbb R^4$, $t(y) = y_3$ is its time and
$\vec y = (y_0, y_1, y_2)$ its spatial part.
Configurations of $n$ points are elements of $(\mathbb R^4)^n$, a Euclidean
space with the norm $\|x\|^2 = \sum_i \|x_i\|^2$. A joint test function on
$n$ points is a Schwartz function $(\mathbb R^4)^n \to \mathbb C$.

**Inserting a point.** For a slot $j \in \{0, \dots, n\}$, the
**insertion map** at $j$ is

$$
\sigma_j : (\mathbb R^4)^n \times \mathbb R^4 \to (\mathbb R^4)^{n+1}, \qquad
\sigma_j(x, y) = \operatorname{ins}_j(x; y) = (x_0, \dots, x_{j-1},\ y,\ x_j, \dots, x_{n-1}),
$$

which puts the point $y$ in slot $j$ ([insertion into a slot](../stress-current/slot-insertion.md)).
It is a real-linear bijection, and an isometry when the product carries the
norm $\|(x, y)\|^2 = \|x\|^2 + \|y\|^2$; in particular it is a continuous
linear isomorphism with continuous inverse. For a joint test function $M$ on
$n$ points and a Schwartz function $h$ on $\mathbb R^4$, the **joint test with
$h$ in slot $j$** is the joint test function on $n+1$ points

$$
\big(M \otimes_j h\big)\big(\sigma_j(x, y)\big) = M(x)\, h(y)
\qquad (x \in (\mathbb R^4)^n,\ y \in \mathbb R^4),
$$

that is, the product $(x, y) \mapsto M(x)\, h(y)$ composed with
$\sigma_j^{-1}$: it evaluates $M$ on the points outside slot $j$, in their
order, and $h$ on the point in slot $j$.

**Data.** Fix a Wilson family and let $S$ be a Euclidean correlation table
for its tokens, with quotient label spaces $F_d$ and common label space
$\mathbb F$, and write
$[\beta]_4 \in \mathbb F$ for the image of $\beta \in F_4$. Let $W$ be
boundary distributions over $S$: for every $n$, a complex-multilinear map
$v \mapsto W_n(v)$ from $\mathbb F^n$ to tempered distributions on
$(\mathbb R^4)^n$. Let $K$ be a [Killing field](../stress-current/killing-field.md), with
component $K^b(y)$ of its real value at $y$ along the axis $b$ and
Killing-weighted tests $(K^b h)(y) = K^b(y)\, h(y)$ ([weighted tests](killing-weighted-tests.md)),
and let $T = (T_{ab})$ be a stress tensor of $S$, $T_{ab} \in F_4$. Let
$\zeta_3 = -\mathrm i$ and $\zeta_b = 1$ for spatial $b$ be the Wick factors of
the [Minkowski stress labels](../stress-current/minkowski-stress-field.md).

**The tested insertion.** For labels $v \in \mathbb F^n$, a slot
$j \in \{0, \dots, n\}$, a joint test function $M$ on $n$ points, a Schwartz
function $g \in \mathcal S(\mathbb R^3)$ of space and a Schwartz function
$f \in \mathcal S(\mathbb R)$ of time, with product test
$(g \otimes f)(y) = g(\vec y)\, f(t(y))$, the **tested stress insertion** in slot
$j$ is the complex number

$$
\mathcal J_j(v; M, g, f) = \sum_{b=0}^{3} \zeta_b\
W_{n+1}\big(\operatorname{ins}_j(v;\ [T_{3b}]_4)\big)\Big( M \otimes_j \big(K^b\,(g \otimes f)\big) \Big).
$$

The label $[T_{3b}]_4$ of the stress component with first index the time axis
sits in slot $j$ and the labels $v$ fill the other slots in order; the joint
test is $M$ in the original variables times
$y \mapsto K^b(y)\, g(\vec y)\, f(t(y))$ in the inserted variable $y$. No
support or reality condition on $M$, $g$ or $f$ is part of the definition.

## Depends on

- [Killing fields](../stress-current/killing-field.md)
- [Minkowski stress labels and the stress field](../stress-current/minkowski-stress-field.md)
- [Insertion into a slot](../stress-current/slot-insertion.md)
- [Test functions weighted by a Killing field](killing-weighted-tests.md)

## Sources

- [YM/EveryPhase ledger: Decree](../../../sources/every-phase.md#decree)
- [YM/EveryPhase ledger: Frost](../../../sources/every-phase.md#frost)
- [YM/EveryPhase ledger: Slots](../../../sources/every-phase.md#slots)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
