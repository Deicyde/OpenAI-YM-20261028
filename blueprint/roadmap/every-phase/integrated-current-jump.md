# Spatially integrated current and its jump

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$. Fix a Wilson
family and let $S$ be a Euclidean correlation table for its tokens, with
quotient label spaces
$F_d$ and common label space $\mathbb F$, and write $[\beta]_4 \in \mathbb F$
for the image of $\beta \in F_4$. Let $W$ be boundary distributions over $S$
(a complex-multilinear map $v \mapsto W_n(v)$ from $\mathbb F^n$ to tempered
distributions on $(\mathbb R^4)^n$ for every $n$), let $Z$ be a Laplace family
for $W$ (for every $n$ and every complex configuration
$\zeta \in (\mathbb C^4)^n$, a Schwartz function $\ell_n(\zeta)$ on
$(\mathbb R^4)^n$, equal to
$y \mapsto e^{\mathrm i\, y\cdot\operatorname{Re}\zeta}\, e^{-\operatorname{Im}\zeta\cdot y}\,\chi_n(y)$
(with $\cdot$ the Euclidean inner product of $(\mathbb R^4)^n$) when $\operatorname{Im}\zeta$ has consecutive differences in the open forward
cone; here $\chi_n$ is a fixed cutoff function on $(\mathbb R^4)^n$: real, of
temperate growth, equal to $1$ at points at Euclidean distance less than $1$
from the cone $C_n$ of those $q \in (\mathbb R^4)^n$ with
$\sum_i h_i\, (\Lambda q_i)_3 \ge 0$ for every proper orthochronous Lorentz
transformation $\Lambda$ and every nondecreasing $h \in \mathbb R^n$, and with closed support inside the points
at distance less than $3$ from $C_n$), and let

$$
\widetilde Z(v; \zeta) = (2\pi)^{-4n}\, \widehat{W_n(v)}\big(\ell_n(\zeta)\big) \qquad (v \in \mathbb F^n,\ \zeta \in (\mathbb C^4)^n)
$$

be its continued function, $\widehat{W_n(v)}$ the Fourier transform of
$W_n(v)$: $\widehat{W_n(v)}(f) = W_n(v)(\hat f)$ with
$\hat f(q) = \int e^{-\mathrm i\, y\cdot q} f(y)\, dy$.

**Complex points.** For $r \in \mathbb R^3$ and $z \in \mathbb C$, let
$\langle r, z\rangle \in \mathbb C^4$ be the complex point with spatial
coordinates $r_0, r_1, r_2$ and time coordinate $z$. For spatial
positions $\xi \in (\mathbb R^3)^n$ and complex times $u \in \mathbb C^n$, let
$\langle \xi, u\rangle \in (\mathbb C^4)^n$ be the complex configuration with
points $\langle \xi_i, u_i\rangle$. For a slot $j \in \{0, \dots, n\}$, a
spatial point $r \in \mathbb R^3$ and a complex time $z$, put

$$
\zeta^j(\xi, u; r, z) = \big\langle \operatorname{ins}_j(\xi; r),\ \operatorname{ins}_j(u; z) \big\rangle \in (\mathbb C^4)^{n+1},
$$

the configuration with the point $\langle r, z\rangle$ in slot $j$ and the
points $\langle \xi_i, u_i\rangle$, in order, in the other slots
([insertion into a slot](slot-insertion.md)).

**Currents.** Fix a [Killing field](killing-field.md) $K$, with complexified
components $w^K_b$; a stress tensor $T = (T_{ab})$ of $S$, $T_{ab} \in F_4$;
labels $v \in \mathbb F^n$; and a Schwartz function $g$ on $\mathbb R^3$. For a
slot $j \in \{0, \dots, n\}$ and an axis $a$, the **current density** at a
complex configuration $\zeta \in (\mathbb C^4)^{n+1}$ is

$$
\tau^j_a(\zeta) = \sum_{b=0}^{3} w^K_b(\zeta_j)\ \widetilde Z\big(\operatorname{ins}_j(v; [T_{ab}]_4);\ \zeta\big),
$$

where $\zeta_j \in \mathbb C^4$ is the point of $\zeta$ in slot $j$. The
**integrated current** with the stress in slot $j$ at complex time $z$ is

$$
I^j(\xi, u; z) = \int_{\mathbb R^3} g(r)\ \tau^j_3\big(\zeta^j(\xi, u; r, z)\big)\, dr ,
$$

a Lebesgue integral over $\mathbb R^3$, taken to be $0$ when the integrand is
not integrable. It integrates the time component $a = 3$ of the current over
the spatial position $r$ of the inserted stress.

**Base points and the jump.** A **base point** for $n$ points is a triple
$p = (\xi, u, t)$ of spatial positions $\xi \in (\mathbb R^3)^n$, complex times
$u \in \mathbb C^n$ and a real shift $t \in \mathbb R$; base points form the
space $(\mathbb R^3)^n \times \mathbb C^n \times \mathbb R$ with its product
topology. For a slot $k \in \{0, \dots, n-1\}$ and $s \in \mathbb R$, the
current **just after** and **just before** the point $k$ are

$$
I^{\uparrow}_k(p, s) = I^{k+1}\big(\xi, u;\ u_k + t + \mathrm i s\big),
\qquad
I^{\downarrow}_k(p, s) = I^{k}\big(\xi, u;\ u_k + t - \mathrm i s\big).
$$

In the first the stress occupies slot $k+1$, immediately after the entry with
index $k$; in the second it occupies slot $k$, immediately before it. The
**current jump** at slot $k$ is

$$
J_k(p, s) = I^{\uparrow}_k(p, s) - I^{\downarrow}_k(p, s).
$$

It depends on $Z$, $K$, $T$, $v$, $g$ and $k$.

## Depends on

- [Killing fields](killing-field.md)
- [Insertion into a slot](slot-insertion.md)

## Sources

- [YM/EveryPhase ledger: Cross](../../sources/every-phase.md#cross)
- [YM/EveryPhase ledger: Strip](../../sources/every-phase.md#strip)
- [YM/EveryPhase ledger: Killing](../../sources/every-phase.md#killing)
- [YM/EveryPhase ledger: Slots](../../sources/every-phase.md#slots)
- [YM/EveryPhase ledger: Docks](../../sources/every-phase.md#docks)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
