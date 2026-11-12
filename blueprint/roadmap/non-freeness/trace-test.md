# Trace test

Let $(n, G, \mathfrak g)$ be a matrix gauge group, $C$ a Wilson family for it,
and $T$ a continuum hierarchy over $C$. The conditions below use the following
objects.

- $\mathfrak g$ is the Lie algebra of the gauge group, a real linear subspace
  of the complex $(n+1)\times(n+1)$ matrices, and $\dim_{\mathbb R} \mathfrak g$
  is its dimension as a real vector space.
- $T$ carries a Hilbert space $H$, whose inner product
  $\langle \cdot, \cdot \rangle$ is conjugate-linear in its first argument, a
  space $L$ of field labels, and a Wightman theory on $H$ and $L$. The field
  system of this theory consists of a complex linear subspace $D$ of $H$, the
  domain; a vector $\Omega \in D$, the vacuum; and, for every label $a \in L$
  and every Schwartz test function $f \in \mathcal S(\mathbb R^4)$, a
  complex-linear map $\varphi(a, f) : D \to D$, the smeared field, which
  depends complex-linearly on $a$ and complex-linearly on $f$. Here
  $\mathcal S(\mathbb R^4)$ is the space of Schwartz test functions
  $f : \mathbb R^4 \to \mathbb C$.
- $T$ carries the field space $F_4$ of grade $4$, a finite-dimensional
  complex normed space, a complex-linear map $\iota_4 : F_4 \to L$, and a
  vector $\Theta \in F_4$, its centered trace.
- $\Gamma_T : \mathbb R \to \mathbb C$ is the trace two-point function of
  $T$: $\Gamma_T(r)$ is the correlation of $T$, in the phase of its selected
  character, of two copies of the graded field $(4, \Theta)$ at the points
  $(0, 0, 0, -r/2)$ and $(0, 0, 0, r/2)$ of $\mathbb R^4$, whose last
  coordinate is time.
- For a finite list $\mathbf t$ of pairs of a complex number and a track,
  $\mathrm{Wick}_{\mathbf t} : \mathbb R \to \mathbb C$ is the Wick profile of
  $\mathbf t$.

The logarithm $\log$ is the natural logarithm, and $|w|$ is the modulus of a
complex number $w$. The hierarchy $T$ **passes the trace test** when the
following four conditions hold. They are conditions on $T$ and add no data.

1.  *Centered.* For every Schwartz test function
    $f \in \mathcal S(\mathbb R^4)$,

    $$
    \bigl\langle \Omega,\ \varphi\bigl(\iota_4(\Theta), f\bigr)\, \Omega \bigr\rangle = 0 .
    $$

2.  *Positive amplitude.*

    $$
    \frac{3 \dim_{\mathbb R} \mathfrak g}{\pi^4} > 0 .
    $$

3.  *Short-distance behaviour.* As $r$ tends to $0$ through positive values,

    $$
    r^8 \bigl(\log(1/r)\bigr)^2 \, \Gamma_T(r) \longrightarrow \frac{3 \dim_{\mathbb R} \mathfrak g}{\pi^4}
    $$

    in $\mathbb C$: for every $\varepsilon > 0$ there is $\delta > 0$ such that
    $\bigl| r^8 (\log(1/r))^2 \, \Gamma_T(r) - 3 \dim_{\mathbb R} \mathfrak g / \pi^4 \bigr| < \varepsilon$
    for every real $r$ with $0 < r < \delta$.

4.  *Exclusion of Wick profiles.* For every finite list $\mathbf t$ of pairs of
    a complex number and a track, there is no $\delta > 0$ such that
    $\Gamma_T(r) = \mathrm{Wick}_{\mathbf t}(r)$ for every real $r$ with
    $0 < r < \delta$. Equivalently, for every $\delta > 0$ there is a real $r$
    with $0 < r < \delta$ and $\Gamma_T(r) \neq \mathrm{Wick}_{\mathbf t}(r)$.

The four conditions are separate requirements. The first concerns the field
system of the Wightman theory of $T$; the second involves only the Lie algebra
$\mathfrak g$, not the hierarchy; the third and fourth concern the trace
two-point function. The fourth excludes only exact agreement on an interval
$(0, \delta)$, and only with the Wick profiles of finite lists.

## Depends on

- [Continuum hierarchy](../continuum-hierarchy/hierarchy.md)
- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](../wilson-lattice/wilson-family.md)
- [Schwartz test functions](../spacetime/schwartz-test-functions.md)
- [Wightman theory data](../wightman/wightman-theory.md)
- [Field system](../wightman/field-system.md)
- [Two-point function of the centered trace](trace-two-point-function.md)
- [Wick profiles](wick-profiles.md)

## Sources

- [ChallengeSpec.lean ledger: trace test](../../sources/challenge-spec.md#trace-test)
- [Upstream description: non-freeness test](../../sources/upstream-readme.md#non-freeness-test)
