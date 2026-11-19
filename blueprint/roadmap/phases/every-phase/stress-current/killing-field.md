# Killing fields

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$; $\zeta_b$ is
the Wick factor of the
[Minkowski stress labels](minkowski-stress-field.md), $\zeta_3 = -\mathrm i$
and $\zeta_b = 1$ for spatial $b$. Let $\theta = \mathrm{diag}(1, 1, 1, -1)$ be
the time reflection of $\mathbb R^4$.

A **Killing field** $K = (k, V)$ consists of

- a translation $k = (k_0, k_1, k_2, k_3) \in \mathbb R^4$, and
- a real $4 \times 4$ matrix $V = (V_{bc})$, indexed by the axes, satisfying
  the tangent condition

    $$
    V^{\mathsf T} = -\,\theta V \theta .
    $$

Since $\eta = \mathrm{diag}(-1, -1, -1, 1) = -\theta$, the tangent condition
says $V^{\mathsf T}\eta + \eta V = 0$: $V$ is an infinitesimal Lorentz
transformation.

The **real value** of $K$ at a point $x \in \mathbb R^4$ is

$$
K(x) = k + V x \in \mathbb R^4 .
$$

The **complexified component** of $K$ along an axis $b$ at a complex point
$z = (z_0, z_1, z_2, z_3) \in \mathbb C^4$ is

$$
w^K_b(z) = \zeta_b \Big( k_b + \sum_{c=0}^{3} V_{bc}\, z_c \Big) \in \mathbb C .
$$

With the rotation factors $\kappa_3 = \mathrm i$ and $\kappa_c = 1$ for spatial
$c$ (not the Wick factors $\zeta$ above, whose time entry is $-\mathrm i$), the **Euclidean column** of $K$ along $b$ at a Euclidean point
$y \in \mathbb R^4$ is the complexified component at the Wick-rotated point
$(\kappa_0 y_0, \kappa_1 y_1, \kappa_2 y_2, \kappa_3 y_3)$:

$$
K^b_{\mathrm E}(y) = w^K_b(\kappa_0 y_0, \dots, \kappa_3 y_3)
= \zeta_b \Big( k_b + \sum_{c=0}^{3} V_{bc}\, \kappa_c\, y_c \Big).
$$

## Depends on

- [Minkowski stress labels and the stress field](minkowski-stress-field.md)

## Sources

- [YM/EveryPhase ledger: Killing](../../../../sources/every-phase.md#killing)
- [Armstrong's informalization: unit V.3](../../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
