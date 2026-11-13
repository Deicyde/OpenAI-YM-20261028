# Stress charge and the commutator action

A point of spacetime is $x = (x_0, x_1, x_2, x_3) \in \mathbb R^4$, with time
$t(x) = x_3$, the last coordinate, and spatial part
$\vec x = (x_0, x_1, x_2) \in \mathbb R^3$; the axes are numbered
$0, 1, 2, 3$, with time the axis $3$.

Let $S$ be a Euclidean correlation table of the construction, with quotient
label spaces $F_d$, common label space $\mathbb F$, and
$[\beta]_d \in \mathbb F$ the image of $\beta \in F_d$ under the
complex-linear map $\beta \mapsto [\beta]_d$ of $F_d$ into $\mathbb F$. Let
$\mathfrak W$ be Wightman data over $S$. Its field system consists of a
Hilbert space $H$, a complex linear subspace $D \subseteq H$ (the domain), a
vacuum $\Omega \in D$ and, for every label $\ell \in \mathbb F$ and Schwartz
test function $h \in \mathcal S(\mathbb R^4)$, a complex-linear map
$\varphi(\ell, h) : D \to D$ depending complex-linearly on $\ell$ and on $h$.
Let $T = (T_{ab})$ be a stress tensor of $S$ and $T_{ab}(h)$ its
[stress field](../stress-current/minkowski-stress-field.md) in $\mathfrak W$: the field of
$[-\zeta_a\zeta_b T_{ab}]_4 \in \mathbb F$, the image of the Minkowski stress
label $-\zeta_a\zeta_b T_{ab} \in F_4$ under the map
$\beta \mapsto [\beta]_4$, smeared with $h$, where $\zeta_3 = -\mathrm i$ and
$\zeta_a = 1$ for the spatial axes $a \in \{0, 1, 2\}$. Let $K = (k, V)$ be a
[Killing field](../stress-current/killing-field.md), with value $K(x) = k + Vx \in \mathbb R^4$
at $x$, and write $K^b(x) = k_b + \sum_{j=0}^{3} V_{bj} x_j$ for its component
along the axis $b$. For a test function $h$, $K^b h$ is the
[Killing-weighted test](../ward-identities/killing-weighted-tests.md), the Schwartz function
$x \mapsto K^b(x)\, h(x)$.

**The charge.** For a Schwartz function $f \in \mathcal S(\mathbb R)$ of time
and a Schwartz function $g \in \mathcal S(\mathbb R^3)$ of space, let
$g \otimes f \in \mathcal S(\mathbb R^4)$ be the Schwartz function
$(g \otimes f)(x) = g(\vec x)\, f(t(x))$. The **stress charge** of
$\mathfrak W$, $K$ and $T$ with time profile $f$ and spatial cutoff $g$ is the
complex-linear map

$$
\mathcal Q_K(f, g) = \sum_{b=0}^{3} T_{3b}\big(K^b\, (g \otimes f)\big) : D \to D,
$$

the stress field with first index the time axis $3$, tested with
$x \mapsto K^b(x)\, g(\vec x)\, f(t(x))$ and summed over the second index $b$.
The definition places no condition on $f$ or $g$.

**The commutator action.** For complex-linear maps $A, B : D \to D$, write
$[A, B] = AB - BA$, where $AB$ is the composite in which $B$ is applied first.
The **commutator action** of $A$ on $B$ is the complex-linear map

$$
\mathrm i\,[A, B] = \mathrm i\,\big(A B - B A\big) : D \to D.
$$

## Depends on

- [Killing fields](../stress-current/killing-field.md)
- [Minkowski stress labels and the stress field](../stress-current/minkowski-stress-field.md)
- [Test functions weighted by a Killing field](../ward-identities/killing-weighted-tests.md)

## Sources

- [YM/EveryPhase ledger: Charge](../../../sources/every-phase.md#charge)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
