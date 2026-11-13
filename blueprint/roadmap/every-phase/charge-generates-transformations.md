# Charges generate the transformations of fields

Fix a Wilson family and let $S$ be a Euclidean correlation table for its
tokens, with quotient
label spaces $F_d$, common label space $\mathbb F$, and
$[\beta]_d \in \mathbb F$ the image of $\beta \in F_d$; a graded label is a
pair $(d, \beta)$ with $\beta \in F_d$. Let $\mathfrak W$ be Wightman data
over $S$, with domain $D$ and smeared fields $\varphi(a, h) : D \to D$, let
$T$ be a stress tensor of $S$, and let $R$ be rotations of $S$. The support
$\operatorname{supp} m$ of a function is the closure of the set where it is
not zero.

$\mathfrak W$, $T$ and $R$ satisfy the condition that **charges generate the
transformations of fields** when, for every compact set
$\mathcal O \subseteq \mathbb R^4$, every
[admissible time profile](admissible-time-profile.md) $f$, every
[admissible spatial cutoff](admissible-spatial-cutoff.md) $g$ for
$\mathcal O$ and $f$, every graded label $(d, \beta)$, every test function
$m \in \mathcal S(\mathbb R^4)$ with
$\operatorname{supp} m \subseteq \mathcal O$ and every
[Killing field](killing-field.md) $K$, the
[commutator action](stress-charge.md) of the stress charge
$\mathcal Q_K(f, g)$ of $\mathfrak W$, $K$ and $T$ on the field of
$(d, \beta)$ smeared with $m$ is its
[infinitesimal transformation](infinitesimal-field-transformation.md)
$\delta_K(d, \beta; m)$ built with the infinitesimal rotations of $R$:

$$
\mathrm i\,\Big[\mathcal Q_K(f, g),\ \varphi\big([\beta]_d, m\big)\Big]
= \varphi\big([\Sigma^{(d)}_V \beta]_d,\ m\big)
+ \sum_{i=0}^{3} \varphi\big([\beta]_d,\ -\partial_i (K^i m)\big)
$$

as complex-linear maps $D \to D$, where $K = (k, V)$ is the Killing field
with translation $k$ and matrix $V$,
$K^i(x) = k_i + \sum_{j=0}^{3} V_{ij} x_j$ its components, $\partial_i$ the
derivative along the $i$-th standard basis vector, and $\Sigma^{(d)}_V$ the
label action of $V$ on $F_d$.

This is a condition on $\mathfrak W$, $T$ and $R$; it assumes nothing else
about $\mathfrak W$.

## Depends on

- [Killing fields](killing-field.md)
- [Admissible time profile](admissible-time-profile.md)
- [Admissible spatial cutoff](admissible-spatial-cutoff.md)
- [Stress charge and the commutator action](stress-charge.md)
- [Infinitesimal Poincaré transformation of a field](infinitesimal-field-transformation.md)

## Sources

- [YM/EveryPhase ledger: Implement](../../sources/every-phase.md#implement)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
