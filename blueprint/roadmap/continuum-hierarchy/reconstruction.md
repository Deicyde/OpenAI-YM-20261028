# Reconstruction conditions

Let $C$ be a Wilson family for a matrix gauge group, and let $T$ be a
continuum hierarchy over $C$. The conditions below use the following
components of $T$.

- A Hilbert space $H$, whose inner product $\langle \cdot, \cdot \rangle$ is
  conjugate-linear in its first argument; a space $L$ of field labels; and a
  Wightman theory on $H$ and $L$. The field system of this theory consists of
  a domain $D$, a complex linear subspace of $H$, a vacuum $\Omega \in D$
  and, for every label $\ell \in L$ and every Schwartz test function
  $f \in \mathcal S(\mathbb R^4)$, a smeared field $\varphi(\ell, f)$, a
  complex-linear map from $D$ to $D$.
- For every grade $d \in \mathbb N = \{0, 1, 2, \dots\}$, a finite-dimensional
  complex normed space $F_d$ and a complex-linear map $\iota_d : F_d \to L$.
  A **graded field** is a pair $a = (d, u)$ of a grade $d \in \mathbb N$ and a
  vector $u \in F_d$; its label is $\iota(a) = \iota_d(u) \in L$.
- A map $\pi$ that assigns a graded field $\pi(v)$ to every token $v$ of $C$.
- A compact metric space $X$, whose points are called characters, with the
  Borel σ-algebra of its metric topology; a measure $\nu$ on $X$, the phase
  measure; and a selected character $s_0 \in X$.
- The correlations: for every $n \in \mathbb N$, every $s \in X \cup \{*\}$,
  every $n$-tuple $a = (a_0, \dots, a_{n-1})$ of graded fields and every
  configuration $x = (x_0, \dots, x_{n-1}) \in (\mathbb R^4)^n$ of $n$ points,
  a complex number $S_s(a; x)$. Here $*$ is an extra value, not a character,
  and $S_*$ is the unselected correlation.
- The continuation: for every $n \in \mathbb N$, every $n$-tuple $a$ of graded
  fields, every $n$-tuple $z = (z_0, \dots, z_{n-1}) \in \mathbb C^n$ of
  complex times and every $n$-tuple $\xi = (\xi_0, \dots, \xi_{n-1})$ of
  spatial positions $\xi_k \in \mathbb R^3$, a complex number
  $S^c(a; z, \xi)$.

For a point $y \in \mathbb R^4$, $t(y)$ is its time, its last coordinate, and
$\vec y \in \mathbb R^3$ is its spatial part, formed by its first three
coordinates; $\mathrm i$ is the imaginary unit. For $n \in \mathbb N$, write
$\mathrm{Sep}_n$ for the open set of separated configurations of $n$ points,
those whose points are pairwise distinct, and

$$
\mathcal T_n = \{ z \in \mathbb C^n : \operatorname{Im} z_0 < \operatorname{Im} z_1 < \dots < \operatorname{Im} z_{n-1} \}
$$

for the ordered tube. For a configuration $x \in (\mathbb R^4)^n$, write
$\mathrm i\,t(x) = \big(\mathrm i\,t(x_0), \dots, \mathrm i\,t(x_{n-1})\big) \in \mathbb C^n$
for its imaginary times and
$\vec x = (\vec x_0, \dots, \vec x_{n-1}) \in (\mathbb R^3)^n$ for its spatial
positions; for $r \in \mathbb R$ and
$h = (h_0, \dots, h_{n-1}) \in \mathbb R^n$, write $z_{r,h}(x) \in \mathbb C^n$
for the complex shift of $x$ by $r$ and $h$, whose entry with index $k$ is
$t(x_k) + \mathrm i\, r h_k$; and for Schwartz test functions
$f_0, \dots, f_{n-1}$, write
$(f_0 \otimes \dots \otimes f_{n-1})(x) = \prod_{k=0}^{n-1} f_k(x_k)$ for
their product test. For labels $\ell_0, \dots, \ell_{n-1} \in L$ and Schwartz
test functions $f_0, \dots, f_{n-1}$, the vacuum expectation value of the field
system is

$$
\mathcal W(\ell_0, \dots, \ell_{n-1};\, f_0, \dots, f_{n-1})
= \big\langle \Omega,\ \varphi(\ell_0, f_0)\, \varphi(\ell_1, f_1) \cdots \varphi(\ell_{n-1}, f_{n-1})\, \Omega \big\rangle .
$$

The hierarchy $T$ **satisfies the reconstruction conditions** when the
following fifteen conditions hold. They are conditions on $T$ and add no data.

1.  *Wightman axioms.* The Wightman theory of $T$ satisfies the Wightman
    axioms W0, W1, W2 and W3.
2.  *Faithfulness.* The field system of this theory is faithful: for every
    label $\ell \neq 0$ in $L$ there is a Schwartz test function $f$ such that
    $\varphi(\ell, f)$ is not the zero map of $D$.
3.  *Injectivity.* For every grade $d$, the map $\iota_d$ is injective.
4.  *A nonzero field.* There are a graded field $a$ and a Schwartz test
    function $f$ such that $\varphi(\iota(a), f)$ is not the zero map of $D$.
5.  *Covering of the labels.* Every label $\ell \in L$ is the label
    $\iota(a)$ of some graded field $a$.
6.  *Representation by tokens.* Every graded field is $\pi(v)$ for some token
    $v$ of $C$.
7.  *Normalization.* $\nu$ is a probability measure: $\nu(X) = 1$.
8.  *Full support.* $\nu(U) > 0$ for every nonempty open subset $U$ of $X$.
9.  *Permutation symmetry.* For every $s \in X \cup \{*\}$, every
    $n \in \mathbb N$, every $n$-tuple $a$ of graded fields, every
    $x \in \mathrm{Sep}_n$ and every permutation $\sigma$ of
    $\{0, 1, \dots, n-1\}$,

    $$
    S_s\big(a_{\sigma(0)}, \dots, a_{\sigma(n-1)};\ x_{\sigma(0)}, \dots, x_{\sigma(n-1)}\big)
    = S_s\big(a_0, \dots, a_{n-1};\ x_0, \dots, x_{n-1}\big),
    $$

    the graded fields and the points being permuted together.

10. *Smoothness.* For every $s \in X \cup \{*\}$, every $n \in \mathbb N$ and
    every $n$-tuple $a$ of graded fields, the function $x \mapsto S_s(a; x)$
    is infinitely differentiable on $\mathrm{Sep}_n$ in the real sense: for
    every $m \in \mathbb N$ it is $m$ times continuously differentiable on
    $\mathrm{Sep}_n$, as a map from the real vector space $(\mathbb R^4)^n$
    to $\mathbb C$. The condition asks for smoothness, not for real
    analyticity.
11. *Continuity in the character.* For every $n \in \mathbb N$, every
    $n$-tuple $a$ of graded fields and every $x \in \mathrm{Sep}_n$, the
    function $s \mapsto S_s(a; x)$ from $X$ to $\mathbb C$ is continuous.
12. *Mixture.* For every $n \in \mathbb N$, every $n$-tuple $a$ of graded
    fields and every $x \in \mathrm{Sep}_n$,

    $$
    \int_X S_s(a; x)\, d\nu(s) = S_*(a; x).
    $$

13. *Complex differentiability of the continuation.* For every
    $n \in \mathbb N$, every $n$-tuple $a$ of graded fields and every
    $\xi \in (\mathbb R^3)^n$, the function $z \mapsto S^c(a; z, \xi)$ is
    complex differentiable on the ordered tube $\mathcal T_n$: for every
    $z \in \mathcal T_n$ there is a complex-linear map
    $\lambda : \mathbb C^n \to \mathbb C$ such that

    $$
    S^c(a; w, \xi) = S^c(a; z, \xi) + \lambda(w - z) + o\big(|w - z|\big)
    \qquad \text{as } w \to z \text{ within } \mathcal T_n,
    $$

    where $|w - z| = \max_k |w_k - z_k|$.

14. *Values at imaginary times.* For every $n \in \mathbb N$, every $n$-tuple
    $a$ of graded fields and every configuration $x \in (\mathbb R^4)^n$ whose
    times strictly increase, $t(x_0) < t(x_1) < \dots < t(x_{n-1})$,

    $$
    S^c\big(a;\ \mathrm i\,t(x),\ \vec x\big) = S_{s_0}(a; x).
    $$

15. *Boundary values on product tests.* For every $n \in \mathbb N$, every
    $n$-tuple $a$ of graded fields, all real heights
    $h_0 < h_1 < \dots < h_{n-1}$ and all Schwartz test functions
    $f_0, \dots, f_{n-1}$,

    $$
    \lim_{r \to 0^+} \int_{(\mathbb R^4)^n}
    S^c\big(a;\ z_{r,h}(x),\ \vec x\big)\, (f_0 \otimes \dots \otimes f_{n-1})(x)\, dx
    = \mathcal W\big(\iota(a_0), \dots, \iota(a_{n-1});\ f_0, \dots, f_{n-1}\big).
    $$

The integral in condition 12 is taken over $X$ with respect to $\nu$, and the
one in condition 15 over all of $(\mathbb R^4)^n$ with respect to Lebesgue
measure on $(\mathbb R^4)^n = \mathbb R^{4n}$; both are Bochner integrals of
complex-valued functions, which by convention are $0$ when the integrand is
not integrable. The limit in condition 15 is taken as $r$ tends to $0$ through
positive values. Conditions 9 to 12 constrain the correlations only at
separated configurations. Conditions 9 and 10 are required for every
$s \in X \cup \{*\}$, the unselected correlation included; condition 14
involves only the selected character $s_0$.

## Depends on

- [Continuum hierarchy](hierarchy.md)
- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](../wilson-lattice/wilson-family.md)
- [Wightman theory data](../wightman/wightman-theory.md)
- [The Wightman axioms](../wightman/wightman-axioms.md)
- [Faithful field system](../wightman/faithful-fields.md)
- [Field system](../wightman/field-system.md)
- [Schwartz test functions](../spacetime/schwartz-test-functions.md)
- [Configurations of n points](../spacetime/point-configurations.md)
- [Separated configurations](../spacetime/separated-configurations.md)
- [Complex times and spatial positions](continuation-variables.md)
- [Ordered tube](ordered-tube.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)
- [Imaginary times and spatial positions of a configuration](imaginary-times.md)
- [Complex shift of a configuration](complex-shift.md)
- [Product test functions](product-tests.md)
- [Vacuum expectation values](../wightman/vacuum-expectation-values.md)

## Sources

- [ChallengeSpec.lean ledger: reconstruction](../../sources/challenge-spec.md#reconstruction)
- [Upstream description: Wightman reconstruction](../../sources/upstream-readme.md#wightman-reconstruction)
