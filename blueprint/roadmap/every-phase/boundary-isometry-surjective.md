# The boundary isometry is onto

Fix a Wilson family and two Euclidean correlation tables $S$ and $U$ for its
tokens. For every degree $d$ the graded fields of degree $d$ form the
quotient label space $F_d$ of $S$; the label of $v \in F_d$ is its image in
the common label space $\mathbb F$ of $S$, the span of these images. A point
of spacetime is $q = (q_0, q_1, q_2, q_3) \in \mathbb R^4$, with time
$t(q) = q_3$ and spatial part $\vec q = (q_0, q_1, q_2)$; a momentum $p$ has
energy $p_3$. For a configuration $x = (x_1, \dots, x_n)$ and heights $y$,
$t(x) + \mathrm i y$ is the tuple of complex times $t(x_j) + \mathrm i y_j$
and $\vec x$ the tuple of spatial parts. Inner products are conjugate-linear in the first argument.

**Data.** The lemma concerns the following data.

- An Osterwalder–Schrader space $\mathcal H^{\rm OS}$ of $U$ for the time axis: a
  Hilbert space with a vector $\Psi(b)$ for every word $b$ of
  positive times, whose span is dense and whose inner products are the
  time-reflected Schwinger functions of $U$; a self-adjoint contraction
  semigroup $(e^{-\tau H^{\rm OS}})_{\tau \ge 0}$ (a name for the semigroup;
  no generator enters) and a unitary group of spatial translations,
  commuting and strongly continuous, acting on the vectors $\Psi(b)$ by
  translating the words; the Euclidean vacuum $\omega = \Psi(\varnothing)$;
  and the translation representation $U^{\rm OS}$ of $\mathbb R^4$ that
  combines real-time evolution with the spatial translations.
- Slab operators $\Pi$ on $\mathcal H^{\rm OS}$: for every thickness $\ell \ge 0$ and word $w$ a
  bounded operator $\Pi(\ell, w)$ that maps $\Psi(b)$ to the vector of $w$
  followed by $b$ translated by $\ell$ in time, whenever $w$ lies in the slab of
  thickness $\ell$.
- A reconstruction staging $Y$ for $S$ over $\mathcal H^{\rm OS}$ and $\Pi$. It consists of
  one-point slab operators: for every half-width $\delta \ge 0$ a
  complex-linear map $a \mapsto B_\delta(a)$ from $\mathbb F$ to bounded
  operators on $\mathcal H^{\rm OS}$, realized by $\Pi$ (see below), and
  bounded for each label by $C \delta^{-N}$ on $0 < \delta < 1$; and a
  continuation $\mathsf F$: functions $\mathsf F_n(z, \xi; a_1, \dots, a_n)$
  of complex times $z \in \mathbb C^n$, spatial positions
  $\xi \in (\mathbb R^3)^n$ and labels, multilinear in the labels. The
  continuation is required to equal the vacuum matrix elements of products
  of the $B_\delta$ with the complex-time evolutions and spatial translations
  between consecutive points whenever $0 < \delta < 1$ and the imaginary
  parts of $z$ increase with gaps larger than $4\delta$; to be continuous and
  holomorphic in $z$ where the imaginary parts strictly increase; to take at
  purely imaginary, strictly ordered times the Schwinger values of $U$ on
  labels of $S$; to obey a bound
  $|\mathsf F_n(t(x) + \mathrm i y, \vec x; a)| \le K k^{-L}$ when the gaps of
  $y$ are at least $k \in (0, 1]$; and to have tested values at strictly
  increasing heights that are integrable and continuous in the heights, and
  whose derivative in the real parameter $r$ along a line of heights $y + r h$ is the tested value at
  $y + r h$ against $-\mathrm i$ times the derivative of the test function in
  the direction of the configuration with spatial parts $0$ and times $h_j$.
- Wightman data $\mathfrak W$ for $S$: a Hilbert space $H$, a field domain
  $D$, a vacuum $\Omega \in D$, smeared fields $\varphi(a, f) : D \to D$
  depending complex-linearly on $a$ and on $f$, a conjugate-linear map
  $a \mapsto a^\star$ of $\mathbb F$ (the star operation), for every Lorentz
  transformation $\Lambda$ an invertible linear map $\sigma(\Lambda)$ of $\mathbb F$
  and an invertible linear map of each $F_d$ (the Lorentz action, on labels
  and on graded fields), a strongly continuous unitary representation of the
  Poincaré group on $H$ and an energy–momentum projection-valued measure.
- A field algebra $\mathcal A$ for $S$ (inclusion and derivative maps,
  rotations and a Euclidean stress tensor), boundary distributions $W$ (for
  every $n$, a distribution $W_n(a_1, \dots, a_n; \cdot)$ on Schwartz
  functions of $(\mathbb R^4)^n$, multilinear in the labels), and a bounded
  complex-linear map $J : H \to \mathcal H^{\rm OS}$.

A family $B'$ of complex-linear maps $a \mapsto B'_\delta(a)$ ($\delta \ge 0$)
from $\mathbb F$ to bounded operators on $\mathcal H^{\rm OS}$ is **realized
by** slab operators $\Pi'$ on $\mathcal H^{\rm OS}$ when for $\delta > 0$, every degree $d$ and
every $v \in F_d$, $B'_\delta$ of the label of $v$ is the slab operator
$\Pi'(2\delta, w)$ of the single point $w$ at the spatial origin and time
$\delta$ carrying the fixed representative of $v$ (the representatives form
a fixed linear section of the quotient $F_d$); no bound is required. For
such a family, half-width $\delta$, labels $a \in \mathbb F^n$, heights $y$
and a configuration $x \in (\mathbb R^4)^n$, the **Euclidean word vector**
$\Psi^{B'}_\delta(a; x + \mathrm i y)$ at complex times
$t(x_j) + \mathrm i y_j$ and spatial positions $\vec x_j$ is obtained from
$\omega$ by applying $B'_\delta(a_n)$, then the complex-time evolution and
spatial translation from the $(n-1)$-th to the $n$-th point, shortened in
Euclidean time by $2\delta$, then $B'_\delta(a_{n-1})$, and so on, and
finally, after $B'_\delta(a_1)$, the complex-time evolution and spatial
translation from the origin to the first point, shortened in Euclidean time
by $\delta$. Write $\Psi_\delta = \Psi^{B}_\delta$ for the operators $B$ of
$Y$. A pair $(\delta, y)$ is **admissible** when $0 < y_1 < \dots < y_n$,
$0 < \delta < 1$, $4\delta < y_1$ and $4\delta < y_{j+1} - y_j$ for all $j$.

**Hypotheses.**

1. *Boundary-isometry property of $J$.* (a) $J$ is isometric, $J\Omega = \omega$,
   and $J$ intertwines the translations of $\mathfrak W$ with $U^{\rm OS}$;
   (b) some family $B'$ is realized by some slab operators on $\mathcal H^{\rm OS}$; (c) for
   every $n$ and labels $a \in \mathbb F^n$ there is a continuous linear map
   $\Phi_a$ from Schwartz functions on $(\mathbb R^4)^n$ to $H$ with
   $\Phi_a(f_1 \otimes \dots \otimes f_n) = \varphi(a_1, f_1) \cdots \varphi(a_n, f_n)\, \Omega$,
   such that for all slab operators $\Pi'$ on $\mathcal H^{\rm OS}$, every family $B'$
   realized by $\Pi'$ and every Schwartz function $g$,
   $\int g(x)\, \Psi^{B'}_\delta(a; x + \mathrm i y)\, dx \to J \Phi_a(g)$ as
   $y \to 0$ through admissible pairs $(\delta, y)$.
2. *Analytic compatibility of $Y$ with $\mathcal A$, the Lorentz action and
   star operation of $\mathfrak W$, and $W$.* None of the clauses below
   involves $\mathcal A$, so $\mathcal A$ is arbitrary. (a) $W$ is invariant
   under translations and under Lorentz transformations acting on labels
   through the Lorentz action of $\mathfrak W$; for strictly increasing
   heights $y$ and every compactly supported test function $f$, the Fourier
   transform of $W_n$ tested on $f$ equals the continuation of $Y$ at heights
   $y$ tested against the Fourier transform of
   $x \mapsto e^{\sum_j y_j\, t(x_j)} f(x)$; and the Fourier transform of
   each $W_n$ is supported in the closed set of
   $(p_1, \dots, p_n) \in (\mathbb R^4)^n$ with
   $\sum_j y_j\, (p_j)_3 \ge 0$ for every nondecreasing real tuple $y$.
   (b) There are cutoffs and a holomorphic extension of the Fourier–Laplace
   transform of $W$ to the forward tube that reproduces the partial boundary
   values and agrees with the continuation of $Y$ at strictly ordered
   imaginary heights. (c) For every such extension, every $n$, all labels and
   every adjacent pair of indices there are heights tending to zero at which
   exchange data for that pair exist. (d) A label all of whose
   $W$-expectation values vanish is $0$. (e) For a word
   $\beta = ((a_1, f_1), \dots, (a_n, f_n))$ of labels and Schwartz test
   functions, with $a = (a_1, \dots, a_n)$, and for $\varepsilon > 0$, put
   $\delta_\varepsilon = \min(\varepsilon, 1)/8$ and
   $y_\varepsilon = (\varepsilon, 2\varepsilon, \dots, n\varepsilon)$. Then
   $x \mapsto f_1(x_1) \cdots f_n(x_n)\, \Psi_{\delta_\varepsilon}(a; x + \mathrm i y_\varepsilon)$
   is integrable. Writing $\widetilde\Psi_\varepsilon[\beta]$ for its integral,
   for every second word $\gamma$ of the same kind,
   $\langle \widetilde\Psi_\varepsilon[\beta], \widetilde\Psi_{\varepsilon'}[\gamma] \rangle \to W(\beta^\dagger \gamma)$
   as $\varepsilon, \varepsilon' \to 0^+$ independently, where $\beta^\dagger$
   reverses $\beta$ and replaces each letter $(a_j, f_j)$ by $(a_j^\star, \bar f_j)$,
   and $W$ of a word is $W_n$ of its labels tested on the product of its test
   functions. For every $c \in \mathbb R^4$ and $\varepsilon > 0$,
   $\widetilde\Psi_\varepsilon$ of the word with letters $(\sigma(1)\, a_j, f_j(\cdot - c))$
   is $U^{\rm OS}(c)\, \widetilde\Psi_\varepsilon[\beta]$, where $\sigma(1)$ is the map
   of $\mathbb F$ that the Lorentz action of $\mathfrak W$ assigns to the
   identity transformation.
3. *$U$ is symmetric*: its Schwinger functions at configurations of distinct
   points are unchanged when points and tokens are permuted together.
4. *$U$ is smooth*: its Schwinger functions are infinitely differentiable on
   configurations of distinct points.
5. *$U$ respects $S$*: in every degree, the null space of $S$ is contained in
   the null space of $U$.
6. *Reflection Gram identity.* For admissible $(\delta, y)$ and
   $(\delta', y')$ of lengths $n$ and $m$, labels $a \in \mathbb F^n$,
   $a' \in \mathbb F^m$ and configurations $x, x'$,
   $\langle \Psi_\delta(a; x + \mathrm i y), \Psi_{\delta'}(a'; x' + \mathrm i y') \rangle$
   equals $\mathsf F_{n+m}$ at the points $x_n, \dots, x_1, x'_1, \dots, x'_m$
   with heights $-y_n, \dots, -y_1, y'_1, \dots, y'_m$ and labels
   $a_n^\star, \dots, a_1^\star, a'_1, \dots, a'_m$.
7. *Non-tangential boundary values.* For every $n$, labels $a$ and Schwartz
   function $g$, $x \mapsto \mathsf F_n(t(x) + \mathrm i y, \vec x; a)\, g(x)$
   is integrable for strictly increasing $y$, and its integral tends to
   $W_n(a; g)$ as $y \to 0$ through strictly increasing heights.

**Lemma.** Under hypotheses 1 to 7, $J$ is surjective: every vector of
$\mathcal H^{\rm OS}$ is $J \psi$ for some $\psi \in H$.

The lemma is general: $U$, $\mathcal H^{\rm OS}$, $\Pi$, $Y$, $\mathfrak W$ and $J$ are
arbitrary data subject to the hypotheses, and no uniqueness of the vacuum is
assumed on either side.

## Depends on

This node has no prerequisites.

## Sources

- [YM/EveryPhase ledger: Surjective](../../sources/every-phase.md#surjective)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
