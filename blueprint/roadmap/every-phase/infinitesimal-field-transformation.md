# Infinitesimal Poincaré transformation of a field

A point of spacetime is $x = (x_0, x_1, x_2, x_3) \in \mathbb R^4$; the axes
are numbered $0, 1, 2, 3$, with time the axis $3$, the last coordinate. Let
$S$ be a Euclidean correlation table of the construction, with quotient label
spaces $F_d$, common label space $\mathbb F$, and $[\beta]_d \in \mathbb F$
the image of $\beta \in F_d$. A graded label is a pair $(d, \beta)$ with
$\beta \in F_d$. Let $\mathfrak W$ be Wightman data over $S$, with domain $D$
and smeared fields $\varphi(\ell, h) : D \to D$ for $\ell \in \mathbb F$ and
$h \in \mathcal S(\mathbb R^4)$.

**Rotations.** Rotations $R$ of $S$ consist, for every degree $d$, of a map
assigning to every orthogonal $4 \times 4$ matrix a complex-linear
isomorphism of $F_d$ (no group law is required) and of a real-linear map
$\lambda_d$ from the real skew-symmetric $4 \times 4$ matrices to the
complex-linear maps $F_d \to F_d$, the infinitesimal rotations. Only the
infinitesimal rotations enter below.

**Label action of a matrix.** For a real $4 \times 4$ matrix $Y$ let
$\operatorname{sk} Y = \tfrac12 (Y - Y^{\mathsf T})$ be its skew-symmetric
part, and let $\theta = \mathrm{diag}(1, 1, 1, -1)$ be the time reflection.
The **label action** of $Y$ on $F_d$ is the complex-linear map

$$
\Sigma^{(d)}_Y = \lambda_d(\operatorname{sk} Y) - \mathrm i\, \lambda_d\Big(\operatorname{sk}\big((Y - \operatorname{sk} Y)\,\theta\big)\Big) : F_d \to F_d ,
$$

which depends real-linearly on $Y$.

**The transformation.** Let $K = (k, V)$ be a
[Killing field](killing-field.md), with component
$K^i(x) = k_i + \sum_{j=0}^{3} V_{ij} x_j$ along the axis $i$, and let
$K^i m$ be the [Killing-weighted test](killing-weighted-tests.md)
$x \mapsto K^i(x)\, m(x)$. Write $\widetilde\partial_i m = -\partial_i m$ for
the [test derivative](minkowski-stress-field.md), with $\partial_i$ the
derivative in the direction of the $i$-th standard basis vector. For a graded
label $(d, \beta)$ and a test function $m \in \mathcal S(\mathbb R^4)$, the
**infinitesimal transformation** of the field of $(d, \beta)$ smeared with $m$
is the complex-linear map

$$
\delta_K(d, \beta; m)
= \varphi\big([\Sigma^{(d)}_V \beta]_d,\ m\big)
+ \sum_{i=0}^{3} \varphi\big([\beta]_d,\ \widetilde\partial_i (K^i m)\big) : D \to D .
$$

The first term transforms the label by the label action of the matrix $V$ of
$K$; in the second, the derivative falls on the product of $m$ with the affine
coefficient $K^i$, and the sum runs over all four axes, time included. The
definition uses only the infinitesimal rotations of $R$, the field system of
$\mathfrak W$, and $K$.

## Depends on

- [Killing fields](killing-field.md)
- [Minkowski stress labels and the stress field](minkowski-stress-field.md)
- [Test functions weighted by a Killing field](killing-weighted-tests.md)

## Sources

- [YM/EveryPhase ledger: Charge](../../sources/every-phase.md#charge)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
