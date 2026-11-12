# Non-freeness test

The fourth of the [four properties](../challenge/hierarchy-properties.md)
that the challenge asks of a continuum hierarchy is the test the upstream
description calls the non-freeness test. It concerns one vector of grade four
that every [continuum hierarchy](../continuum-hierarchy/hierarchy.md) carries
among its data, its centered trace $\Theta$. In the words of the
[upstream description](../../sources/upstream-readme.md#non-freeness-test),
"a centered grade-four field has a two-point function with a positive
short-distance coefficient of three times the real Lie-algebra dimension
divided by π⁴, after multiplication by r⁸ log²(1/r). No finite sum of the
specified mass-shell Wick profiles agrees with it at all sufficiently small
radii." This chapter defines the objects these two sentences speak of and
states the test, which a hierarchy passes when four conditions hold.

The two-point function is read in the selected phase. For every $n$, a
hierarchy assigns a complex correlation to every phase (one of its characters,
or the unselected phase), every $n$-tuple of graded fields and every
configuration of $n$ points. The two-point function $\Gamma(r)$ of the
centered trace is the correlation, in the phase of the selected character, of
two copies of the graded field $(4, \Theta)$ placed at the time pair at $r$,
the points $(0, 0, 0, -r/2)$ and $(0, 0, 0, r/2)$ of $\mathbb R^4$, time
being the last coordinate: in the source's words, "two insertions on the time
axis at -r/2 and r/2". It is defined for every real $r$, and the test looks
only at $r$ tending to $0$ through positive values.

With $\dim_{\mathbb R} \mathfrak g$ the dimension of the gauge group's Lie
algebra as a real vector space and $\log$ the natural logarithm, the test asks
that

$$
r^8 \bigl(\log(1/r)\bigr)^2 \, \Gamma(r) \longrightarrow \frac{3 \dim_{\mathbb R} \mathfrak g}{\pi^4}
\qquad \text{as } r \to 0^+,
$$

and, as a separate condition that involves only the Lie algebra, that this
coefficient be positive.

The Wick profiles are built from what the source calls "elementary mass-shell
kernels, including finite differential orders". A mode consists of a mass
$m \ge 0$, a spatial order $k \in \mathbb N = \{0, 1, 2, \dots\}$, a time
order $\ell \in \mathbb N$ and a continuous function
$P : \mathbb R^3 \to \mathbb R$ with $P(\lambda p) = \lambda^k P(p)$ for every
$p \in \mathbb R^3$ and every $\lambda > 0$, and its kernel is

$$
K(r, p) = \frac{1}{2E} \, E^{\ell} \, P(p) \, e^{-rE},
\qquad E = \sqrt{m^2 + \lVert p \rVert^2},
$$

for real $r$ and $p \in \mathbb R^3$, with $\lVert p \rVert$ the Euclidean
norm and $1/(2E)$ read as $0$ when $E = 0$. A track is a finite family of
modes, and the Wick profile of a finite list of pairs $(c_j, \tau_j)$ of a
complex coefficient and a track is the function
$r \mapsto \sum_j c_j \prod_i \int_{\mathbb R^3} K_{\mu_{j,i}}(r, p) \, dp$,
the product running over the modes $\mu_{j,i}$ of $\tau_j$ and each integral
taken with respect to Lebesgue measure on $\mathbb R^3$. The test asks
that, for every such finite list, the two-point function and the Wick profile
differ at some $r$ in every interval $(0, \delta)$ with $\delta > 0$: only
exact agreement on such an interval is excluded, and only finite lists are
compared.

The remaining condition concerns the Wightman theory of the hierarchy. With
$\Omega$ the vacuum and $\varphi$ the smeared fields of its field system, and
$\iota_4$ the hierarchy's linear map from fields of grade four to labels, the
vacuum expectation
$\langle \Omega, \varphi(\iota_4(\Theta), f)\, \Omega \rangle$ vanishes for
every Schwartz test function $f$. The short-distance condition and the
exclusion concern the correlation in the selected phase instead. The
hierarchy's [reconstruction conditions](../continuum-hierarchy/reconstruction.md)
relate its correlation in the selected phase, through its continuation, to its
Wightman theory; in the words of the
[upstream description](../../sources/upstream-readme.md#wightman-reconstruction),
"analytic continuation recovers the selected Euclidean hierarchy at ordered
imaginary times and its Wightman vacuum moments on product tests".

The upstream passage on the test ends with a sentence about the detailed
theorem, which this book does not yet map: "The detailed theorem identifies this field as the physical
centered stress trace and supplies the distributional Wick and Maxwell tests."
This book does not yet state that identification. Here the centered trace is the name of a vector of grade four
that the hierarchy carries as data.

## The trace two-point function

The time pair places two points on the time axis of $\mathbb R^4$, at times
$-r/2$ and $r/2$, and the trace two-point function evaluates there the
hierarchy's correlation of two copies of the centered trace in the phase of
the selected character.

- [Two-point function of the centered trace](trace-two-point-function.md)

## Mass-shell Wick profiles

A mode consists of a mass, a spatial and a time order and a continuous
homogeneous numerator on $\mathbb R^3$, and its kernel is a function of a real
number and a point of $\mathbb R^3$. A track is a finite family of modes. The
Wick profile of a finite list of coefficients and tracks adds up, with the
coefficients as weights, the products over each track of the integrals of the
kernels over $\mathbb R^3$.

- [Mass-shell modes and their kernels](mass-shell-modes.md)
- [Wick profiles](wick-profiles.md)

## The test

The trace test collects the four conditions: the vanishing vacuum expectation
of the smeared centered trace, the positivity of the coefficient
$3 \dim_{\mathbb R} \mathfrak g / \pi^4$, the short-distance limit of the
trace two-point function, and the exclusion of the Wick profiles of finite
lists.

- [Trace test](trace-test.md)
