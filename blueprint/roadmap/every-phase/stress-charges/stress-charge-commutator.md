# The stress charge generates the transformation

The axes of spacetime $\mathbb R^4$ are numbered $0, 1, 2, 3$, with time the
axis $3$, the last coordinate; for $v \in \mathbb R^4$, $t(v) = v_3$ is its
time and $\vec v = (v_0, v_1, v_2)$ its spatial part. A point
$v \in \mathbb R^4$ is spacelike when $|t(v)| < \|\vec v\|$, and
$\overline V_+ = \{ v : \|\vec v\| \le t(v) \}$ is the closed forward cone.
The support $\operatorname{supp} m$ of a function is the closure of the set
where it is not zero. Inner products are conjugate-linear in their first
argument.

**Data.** Fix the following.

- Euclidean correlation tables $S$ and $U$ of the construction, with the
  quotient label spaces $F_d$ and common label space $\mathbb F$ of $S$;
  $[\beta]_d \in \mathbb F$ is the image of $\beta \in F_d$, a graded label is
  a pair $(d, \beta)$ with $\beta \in F_d$, and $U(x; v)$ is the value of $U$
  at a configuration $x$ on graded labels $v$ of $S$.
- A stress tensor $T = (T_{ab})$ of $S$, rotations $R$ of $S$ with
  infinitesimal rotations $\lambda_d$, inclusion and derivative maps
  $\rho_{d,e} : F_d \to F_e$ and $\partial^{(d)}_a : F_d \to F_{d+1}$ for
  $S$, and the hypothesis that $S$ satisfies the symmetry and reality
  conditions: at every separated configuration its value does not change when
  a signed permutation of the axes acts on all points and on all labels, and
  conjugating every label conjugates the value. Through this hypothesis each
  $F_d$ carries the conjugate-linear reflection adjoint
  $\beta \mapsto \beta^\dagger$: complex conjugation of the label followed by
  the reflection of the time axis.
- Boundary distributions $W$ of $S$ with cutoff functions $\chi_n$, a Laplace
  family $Z$ for $W$, and a continuation $\mathsf F$, as in the
  [hypotheses for continuing the stress current](../stress-current/stress-continuation-hypotheses.md).
- Wightman data $\mathfrak W$ over $S$: a Hilbert space $H$; a complex linear
  subspace $D \subseteq H$ (the domain), a vacuum $\Omega \in D$ and smeared
  fields $\varphi(\ell, h) : D \to D$, complex-linear maps depending
  complex-linearly on $\ell \in \mathbb F$ and on
  $h \in \mathcal S(\mathbb R^4)$; for every proper orthochronous Lorentz
  transformation $\Lambda$, complex-linear isomorphisms $\sigma(\Lambda)$ of
  $\mathbb F$ and $\sigma_d(\Lambda)$ of each $F_d$ (laws for them appear only
  in hypothesis 4); a conjugate-linear star operation
  $\ell \mapsto \ell^\star$ on $\mathbb F$; a strongly continuous
  representation $g \mapsto \mathcal U(g)$ of the Poincaré coordinates
  $g = (\Lambda, u)$ on $H$ by isometries ($\mathcal U(1)$ is the identity,
  $\mathcal U(g g') = \mathcal U(g)\,\mathcal U(g')$,
  $\|\mathcal U(g)\psi\| = \|\psi\|$, and $g \mapsto \mathcal U(g)\psi$ is
  continuous); and an energy-momentum projection-valued measure $E$ on
  $\mathbb R^4$.

**Hypotheses.**

1. $\mathsf F$, $Z$, $U$, the inclusion and derivative maps, the symmetry and
    reality hypothesis and $T$ satisfy the
    [hypotheses for continuing the stress current](../stress-current/stress-continuation-hypotheses.md).

2. *Euclidean Ward identities of $T$ in $U$.* Let $n \in \mathbb N$, let
    $x = (x_0, \dots, x_n)$ be a configuration of $n + 1$ pairwise distinct
    points, $q = (q_1, \dots, q_n)$ graded labels, and $\varpi$ a window for
    $x$: an infinitely differentiable, compactly supported real function on
    $\mathbb R^4$ equal to $1$ on a neighborhood of $x_0$, with
    $x_1, \dots, x_n \notin \operatorname{supp}\varpi$. Then for every axis
    $b$, degree $d$, $\beta \in F_d$ and real skew-symmetric $4 \times 4$
    matrix $\Xi$,

    $$
    -\sum_{a=0}^{3} \int_{\mathbb R^4} \partial_a\varpi(y)\,
    U\big((y, x); (4, T_{ab}), (d, \beta), q\big)\, dy
    = U\big(x; (d+1, \partial^{(d)}_b \beta), q\big),
    $$

    $$
    -\sum_{a=0}^{3}\sum_{b=0}^{3} \int_{\mathbb R^4} \partial_a\varpi(y)\,
    \big(\Xi\,(y - x_0)\big)_b\,
    U\big((y, x); (4, T_{ab}), (d, \beta), q\big)\, dy
    = U\big(x; (d, \lambda_d(\Xi)\beta), q\big),
    $$

    where $(y, x) = (y, x_0, \dots, x_n)$ carries $(4, T_{ab})$ at $y$,
    $(d, \beta)$ at $x_0$ and $q_i$ at $x_i$; here $\partial_a\varpi$ is the
    derivative of $\varpi$ along the $a$-th standard basis vector, and the
    integrals are Lebesgue integrals, taken to be $0$ when the integrand is
    not integrable.

3. $W$ and $Z$ satisfy the condition of
    [exchange heights for every adjacent pair](../ward-identities/exchange-height-sequences.md).

4. *$\mathfrak W$ realizes $W$ without vacuum uniqueness.* $\mathfrak W$
    satisfies every condition of a Wightman realization of $W$ with the
    rotations $R$ and the symmetry and reality hypothesis, except uniqueness
    of the invariant vector:

    1. $([\beta]_d)^\star = [\beta^\dagger]_d$ for every $d$ and
        $\beta \in F_d$;
    2. $\sigma(\Lambda)[\beta]_d = [\sigma_d(\Lambda)\beta]_d$, $\sigma$ is a
        representation with $\sigma(1)$ the identity,
        $\Lambda \mapsto \sigma_d(\Lambda)\beta$ is continuous, for every
        spatial axis $j$ the derivative at $r = 0$ of
        $r \mapsto \sigma_d(\Lambda_j(r))\beta$, where $\Lambda_j(r)$ is the
        boost of rapidity $r$ along the axis $j$, is
        $-\mathrm i\,\lambda_d(e_{3j} - e_{j3})\beta$, where $e_{ab}$ is the
        matrix with entry $1$ at $(a, b)$ and $0$ elsewhere, $\sigma_d$ agrees
        with the action of $R$ on spatial rotations, and $\sigma_d(\Lambda)$
        commutes with $\beta \mapsto \beta^\dagger$;
    3. $\|\Omega\| = 1$, $D$ is dense in $H$, $D$ is spanned by the vectors
        $\varphi(\ell_1, h_1) \cdots \varphi(\ell_k, h_k)\Omega$, and
        $h \mapsto \varphi(\ell, h)\psi$ is continuous from
        $\mathcal S(\mathbb R^4)$ to $H$ for every $\ell$ and $\psi \in D$;
    4. $\langle \varphi(\ell, h)\psi, \psi' \rangle = \langle \psi, \varphi(\ell^\star, \bar h)\psi' \rangle$
        for all $\ell$, $h$ and $\psi, \psi' \in D$;
    5. $\langle \Omega, \varphi(\ell_1, h_1) \cdots \varphi(\ell_k, h_k)\Omega \rangle
        = W_k(\ell_1, \dots, \ell_k)(h_1 \otimes \dots \otimes h_k)$ for all
        labels and test functions, with
        $(h_1 \otimes \dots \otimes h_k)(x) = \prod_i h_i(x_{i-1})$;
    6. $\varphi(\ell, h)\varphi(\ell', h')\psi = \varphi(\ell', h')\varphi(\ell, h)\psi$
        for $\psi \in D$ whenever $z - z'$ is spacelike for all
        $z \in \operatorname{supp} h$, $z' \in \operatorname{supp} h'$;
    7. for every label $\ell \ne 0$ there is $h$ with $\varphi(\ell, h) \ne 0$;
    8. $\mathcal U(g)$ maps $D$ into $D$ and fixes $\Omega$, and
        $\mathcal U(g)\varphi(\ell, h)\psi = \varphi\big(\sigma(\Lambda)\ell,\ h \circ g^{-1}\big)\,\mathcal U(g)\psi$
        for $g = (\Lambda, u)$, with $(h \circ g^{-1})(x) = h(\Lambda^{-1}(x - u))$;
    9. $\int e^{\mathrm i \langle p, u\rangle}\, d\langle \psi, E(p)\psi\rangle = \langle \psi, \mathcal U(1, u)\psi\rangle$
        for all $\psi \in H$ and $u \in \mathbb R^4$, where
        $\langle p, u\rangle$ is the Euclidean inner product of $\mathbb R^4$;
    10. $E(\mathbb R^4 \setminus \overline V_+) = 0$.

**Statement.** Let $K = (k, V)$ be a [Killing field](../stress-current/killing-field.md),
$(d, \beta)$ a graded label, $\mathcal O \subseteq \mathbb R^4$ a compact set,
$m \in \mathcal S(\mathbb R^4)$ a test function with
$\operatorname{supp} m \subseteq \mathcal O$, $f$ an
[admissible time profile](admissible-time-profile.md), and $c$ an
[admissible spatial cutoff](admissible-spatial-cutoff.md) for $\mathcal O$ and
$f$. Then the [commutator action](stress-charge.md) of the stress charge
$\mathcal Q_K(f, c)$ of $\mathfrak W$, $K$ and $T$ on the field of
$(d, \beta)$ smeared with $m$ is its
[infinitesimal transformation](infinitesimal-field-transformation.md) under
$K$:

$$
\mathrm i\,\Big[\mathcal Q_K(f, c),\ \varphi\big([\beta]_d, m\big)\Big]
= \varphi\big([\Sigma^{(d)}_V \beta]_d,\ m\big)
+ \sum_{i=0}^{3} \varphi\big([\beta]_d,\ -\partial_i (K^i m)\big),
$$

an equality of complex-linear maps $D \to D$: applied to every $\psi \in D$,
the two sides agree. Here $\Sigma^{(d)}_V$ is the label action of the matrix
$V$ of $K$ built from the infinitesimal rotations of $R$,
$K^i(x) = k_i + \sum_{j=0}^{3} V_{ij} x_j$ is the component of $K$ along the
axis $i$, and $\partial_i$ is the derivative along the $i$-th standard basis
vector.

## Depends on

- [Killing fields](../stress-current/killing-field.md)
- [Hypotheses for continuing the stress current](../stress-current/stress-continuation-hypotheses.md)
- [Exchange heights for every adjacent pair](../ward-identities/exchange-height-sequences.md)
- [Admissible time profile](admissible-time-profile.md)
- [Admissible spatial cutoff](admissible-spatial-cutoff.md)
- [Stress charge and the commutator action](stress-charge.md)
- [Infinitesimal Poincaré transformation of a field](infinitesimal-field-transformation.md)

## Proof depends on

- [Ward identity with arbitrary spectators](../ward-identities/ward-identity-schwartz-spectators.md)

## Sources

- [YM/EveryPhase ledger: Charge](../../../sources/every-phase.md#charge)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
