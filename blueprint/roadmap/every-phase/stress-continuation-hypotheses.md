# Hypotheses for continuing the stress current

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$; for
$y \in \mathbb R^4$, $t(y) = y_3$ is its time and $\vec y \in \mathbb R^3$ its
spatial part. A configuration of $n$ points is
$x = (x_0, \dots, x_{n-1}) \in (\mathbb R^4)^n$; it is separated when its
points are pairwise distinct. For $\xi \in (\mathbb R^3)^n$ and
$h \in \mathbb R^n$, $(\xi, h)$ denotes the configuration whose point $i$ has
spatial part $\xi_i$ and time $h_i$. A complex configuration is an element
$\zeta \in (\mathbb C^4)^n$, with real and imaginary parts
$\operatorname{Re}\zeta, \operatorname{Im}\zeta \in (\mathbb R^4)^n$; for real
configurations $x, y$, $x + \mathrm i y$ is the complex configuration with
these parts. Let $V_+ = \{ y \in \mathbb R^4 : \|\vec y\| < t(y) \}$ be the
open forward cone,

$$
\Gamma_n = \{ y \in (\mathbb R^4)^n : y_{i+1} - y_i \in V_+ \text{ for } 0 \le i < n - 1 \},
\qquad
\mathcal T_n = \{ \zeta \in (\mathbb C^4)^n : \operatorname{Im}\zeta \in \Gamma_n \}
$$

the forward heights and the forward tube, and
$\mathcal O_n = \{ z \in \mathbb C^n : \operatorname{Im} z_0 < \operatorname{Im} z_1 < \dots < \operatorname{Im} z_{n-1} \}$.

**Data.** The hypotheses concern the following data.

- A Wilson family and a Euclidean correlation table $S$ for its tokens, with
  quotient label spaces $F_d$ ($d \in \mathbb N$) and common label space $\mathbb F$; for
  $\beta \in F_d$, $[\beta]_d \in \mathbb F$ is its image. A graded label is a
  pair $(d, \beta)$ with $\beta \in F_d$; for a tuple $v$ of graded labels,
  $[v]$ is the tuple of their images in $\mathbb F$.
- A second correlation table $U$, for the same tokens as $S$. For a configuration $x$ of $n$ points and
  graded labels $v_0, \dots, v_{n-1}$, $U(x; v)$ is the value of $U$ at $x$ on
  fixed representatives of the classes $v_i$ (and likewise $S(x; v)$).
- Inclusion and derivative maps for $S$: complex-linear maps
  $\rho_{d,e} : F_d \to F_e$ for $d \le e$, and
  $\partial^{(d)}_a : F_d \to F_{d+1}$ for every degree $d$ and axis $a$.
- The hypothesis that $S$ satisfies the symmetry and reality conditions: at
  every separated configuration, its value does not change when a signed
  permutation of the axes (a permutation of the four axes combined with sign
  changes of some of them) acts on all points and on all labels, and
  conjugating every label conjugates the value. This makes complex
  conjugation of labels descend to conjugate-linear maps
  $\overline{\,\cdot\,} : F_d \to F_d$.
- A stress tensor $T = (T_{ab})$ of $S$, with $T_{ab} \in F_4$.
- Boundary distributions $W$: for every $n$, a complex-multilinear map
  $v \mapsto W_n(v)$ from $\mathbb F^n$ to tempered distributions on
  $(\mathbb R^4)^n$; and for every $n$ a cutoff function: a real function
  $\chi_n$ of temperate growth on $(\mathbb R^4)^n$ that equals $1$ at every
  point at distance less than $1$ from the cone $C_n$ and whose closed support
  lies in the set of points at distance less than $3$ from $C_n$. Here
  $C_n \subseteq (\mathbb R^4)^n$ is the set of $q$ with
  $\sum_i h_i\, t(\Lambda q_i) \ge 0$ for every proper orthochronous Lorentz
  transformation $\Lambda$ (determinant $1$, preserving the Minkowski form and
  the closed forward cone) and every nondecreasing $h \in \mathbb R^n$, and
  distances are Euclidean.
- A continuation $\mathsf F$: for every $n$, complex numbers $\mathsf F_n(z, \xi; v)$ for
  complex times $z \in \mathbb C^n$, spatial positions
  $\xi \in (\mathbb R^3)^n$ and labels $v \in \mathbb F^n$,
  complex-multilinear in $v$.
- A Laplace family $Z$ for $W$: for every $n$ and every complex configuration
  $\zeta$, a Schwartz function $\ell_n(\zeta)$ on $(\mathbb R^4)^n$ such that
  $\ell_n(\zeta)(x) = e^{\mathrm i\, x\cdot\operatorname{Re}\zeta}\, e^{-\operatorname{Im}\zeta\cdot x}\, \chi_n(x)$
  whenever $\zeta \in \mathcal T_n$. Its **continued function** is
  $$
  \widetilde Z(v; \zeta) = (2\pi)^{-4n}\, \widehat{W_n(v)}\big(\ell_n(\zeta)\big),
  $$
  where $\widehat{W_n(v)}$ is the Fourier transform of $W_n(v)$:
  $\widehat{W_n(v)}(f) = W_n(v)(\hat f)$ with
  $\hat f(q) = \int e^{-\mathrm i\, x\cdot q} f(x)\, dx$.

**Hypotheses.** The data satisfy the **hypotheses for continuing the stress
current** when the following seven conditions hold.

1. *Conservation.* For all axes $a, b$: $T_{ab} = T_{ba}$,
   $\overline{T_{ab}} = T_{ab}$, and
   $\sum_{a=0}^{3} \partial^{(4)}_a T_{ab} = 0$.
2. *Euclidean axioms of $U$.* $U$ satisfies the basic laws (permutation
   symmetry at separated configurations, value $1$ on the empty
   configuration, and removal of a point that carries a unit label), the
   same symmetry under signed permutations of the axes and the reality
   condition, translation invariance, reflection positivity in pointwise form
   and in smeared form (including the integrability of the smeared
   integrands), smoothness on separated configurations, and polynomial bounds
   on its derivatives: for every number of points, all labels and every order
   $j$ there are $C \ge 0$ and $A \in \mathbb N$ such that the $j$-th
   derivative in the positions has norm at most $C r^{-A}$ at every
   configuration whose points are pairwise at sup-norm distance at least $r$,
   for every $0 < r \le 1$.
3. *Symmetry of $S$.* $S$ is unchanged when the points of a separated
   configuration and their labels are permuted together.
4. *Inclusions.* For $d \le e$, $\beta \in F_d$, every separated configuration
   $x$ of $n + 1$ points and graded labels $w_0, \dots, w_{n-1}$,
   $S\big(x; (e, \rho_{d,e}\beta), w\big) = S\big(x; (d, \beta), w\big)$, the
   first label sitting at $x_0$.
5. *Derivatives.* For every degree $d$, axis $a$, $\beta \in F_d$, separated
   configuration $x$ of $n + 1$ points and graded labels $w$,
   $U\big(x; (d+1, \partial^{(d)}_a\beta), w\big)$ is the derivative of
   $y \mapsto U\big(y; (d, \beta), w\big)$ at $x$ in the direction that moves
   the coordinate $a$ of the point $y_0$.
6. *$\mathsf F$ continues $U$.* For every $n$ and $v \in \mathbb F^n$: the map
   $(z, \xi) \mapsto \mathsf F_n(z, \xi; v)$ is continuous on
   $\mathcal O_n \times (\mathbb R^3)^n$; and for every $\xi$ the map
   $z \mapsto \mathsf F_n(z, \xi; v)$ is complex differentiable on
   $\mathcal O_n$. For every $n$, every $\xi \in (\mathbb R^3)^n$, every tuple
   $w = (w_0, \dots, w_{n-1})$ of graded labels and every $h \in \mathbb R^n$
   with $h_0 < h_1 < \dots < h_{n-1}$,
   $$
   \mathsf F_n\big((\mathrm i h_0, \dots, \mathrm i h_{n-1}), \xi; [w]\big) = U\big((\xi, h); w\big).
   $$
7. *$Z$ extends $\mathsf F$ over the forward tube.* For every $n$ and
   $v \in \mathbb F^n$: $\widetilde Z(v; \cdot)$ is complex analytic near
   every point of $\mathcal T_n$; for every $y \in \Gamma_n$ and every Schwartz
   function $f$ on $(\mathbb R^4)^n$, the function
   $x \mapsto \widetilde Z(v; x + \mathrm i y) f(x)$ is integrable and
   $$
   \int_{(\mathbb R^4)^n} \widetilde Z(v; x + \mathrm i y)\, f(x)\, dx = W_n(v)^{(y)}(f),
   $$
   where $W_n(v)^{(y)}$ is the distribution obtained by multiplying
   $\widehat{W_n(v)}$ by the damping function
   $m_y(q) = e^{-y\cdot q}\chi_n(q)$ and transforming back,
   $$
   W_n(v)^{(y)}(f) = \widehat{W_n(v)}\big(m_y\, \check f\big),
   \qquad
   \check f(x) = (2\pi)^{-4n} \int e^{\mathrm i\, q\cdot x} f(q)\, dq,
   $$
   with $m_y \check f$ read as $0$ when $m_y$ is not of temperate growth; and
   for every $h \in \mathbb R^n$ with $h_0 < \dots < h_{n-1}$ and every real
   configuration $x$,
   $$
   \widetilde Z\big(v; x + \mathrm i (0, h)\big) = \mathsf F_n\big((t(x_i) + \mathrm i h_i)_i,\ (\vec x_i)_i;\ v\big),
   $$
   with $(0, h)$ the configuration of the points of spatial part $0$ and
   times $h_i$.

The hypotheses add no data. The inner product $x \cdot q$ on $(\mathbb R^4)^n$
is the Euclidean one, and integrals are Lebesgue integrals.

## Depends on

This node has no prerequisites.

## Sources

- [YM/EveryPhase ledger: Cross](../../sources/every-phase.md#cross)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
