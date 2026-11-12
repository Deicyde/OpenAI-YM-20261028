# Continuum hierarchy and Wightman reconstruction

The [upstream description](../../sources/upstream-readme.md#the-public-challenge)
of the public challenge reads: "For each closed matrix subgroup with nonabelian
simple real Lie algebra, choose one Wilson lattice family. For every strictly
increasing sequence of volumes, it has a subsequence and a continuum hierarchy
with the following properties." The four properties that
[the challenge](../challenge/README.md) asks for all concern one and the same
continuum hierarchy. In the words of the
[description of the formal joint existence statement](../../sources/challenge-spec.md#joint-existence),
"All four conclusions concern a single hierarchy on that refinement", and in
those of the
[opening of the formal specification](../../sources/challenge-spec.md#module-docstring),
"All correlation terms, including every spectator in the OPE, are evaluations
of one hierarchy." This chapter defines continuum hierarchies, the variables
at which their continuation is evaluated, the product tests against which it
is integrated, and the reconstruction conditions, the second of the four
properties the challenge asks of a hierarchy.

A hierarchy is built over a fixed Wilson family, which it uses only through
the family's tokens. It carries a Hilbert space $H$, a space of field labels
$L$ and a Wightman theory on $H$ and $L$, given as data: the Wightman axioms
are not part of a hierarchy but one of its reconstruction conditions. For
every grade $d = 0, 1, 2, \dots$ it has a finite-dimensional complex normed
vector space $F_d$ and a complex-linear map $\iota_d : F_d \to L$; a graded
field is a pair $(d, u)$ with $u \in F_d$, and the hierarchy assigns a graded
field $\pi(v)$ to every token $v$ of the family. Its characters form a compact
metric space $X$ with its Borel σ-algebra, and it carries a measure $\nu$ on
$X$, the phase measure, and a selected character $s_0 \in X$. For every
$n = 0, 1, 2, \dots$ it has correlations $S_s(a; x)$ of $n$-tuples $a$ of
graded fields at configurations $x$ of $n$ points of $\mathbb R^4$, one for
every character $s$ and one for an additional value $s = *$ that is not a
character; the correlations at $*$ are called unselected. It also has one
continuation $S^c(a; z, \xi)$, a function of $n$ complex times $z_k$ and $n$
points $\xi_k$ of space $\mathbb R^3$, with no character argument. Finally it
has, for every $j = 0, 1, 2, \dots$, a finite set $\mathrm{Ch}_j$ of channels
with a map $A_j : \mathrm{Ch}_j \to F_j$; coefficients
$C^{j,\kappa}_a(x; o)$, one for every $j$, every channel
$\kappa \in \mathrm{Ch}_j$, every finite family $a$ of graded fields, every
family $x$ of points of $\mathbb R^4$ indexed like $a$, and every further
point $o$ of $\mathbb R^4$; and a vector $\Theta \in F_4$, the centered trace.
The [upstream description](../../sources/upstream-readme.md#non-freeness-test)
says that the detailed theorem, not yet mapped here, identifies the corresponding
field with the physical centered stress trace; inside this book "centered
trace" is only a name.

The four properties read different components of the same hierarchy.
[Wilson origin](../challenge/hierarchy-properties.md) compares the limits of
the smeared lattice moments of tuples of tokens with the unselected
correlations of the graded fields assigned to them, smeared against the same
test functions. The
[operator product expansion](../operator-product-expansion/README.md) bounds
the coefficients and expands the joint correlations of a cluster of graded
fields and a set of spectators, using the channels, the maps $A_j$ and the
coefficients. The [non-freeness test](../non-freeness/README.md) concerns the
centered trace: the vacuum expectation of the smeared field of its label
$\iota_4(\Theta)$ in the Wightman theory, and the correlation of two copies of
it in the selected character. The reconstruction conditions tie the
correlations, the continuation and the Wightman theory together.

Wightman reconstruction is the second of the four themes of the
[upstream description](../../sources/upstream-readme.md#wightman-reconstruction).
Its first two sentences describe the Wightman properties of the selected phase
and its symmetry coordinates, which the
[Wightman chapter](../wightman/README.md) formalizes; the next three concern
the hierarchy itself:

> Analytic continuation recovers the selected Euclidean hierarchy at ordered
> imaginary times and its Wightman vacuum moments on product tests.
> Integrating the character correlations gives the unselected Wilson limit.
> The character measure has full support and the separated correlations vary
> continuously with the character.

In the formal statement, reconstruction consists of fifteen conditions on a
hierarchy. Its one Wightman theory satisfies the Wightman axioms W0–W3, its
field system is faithful, and two conditions tie the continuation to the
correlations of the selected character and to the Wightman theory. First, for
every $n$-tuple of graded fields and every
configuration $x$ of $n$ points whose times strictly increase, the
continuation of these graded fields at the imaginary times and the spatial
positions of $x$ equals their correlation in the selected character at $x$.
Second, take graded fields $(d_k, u_k)$, strictly increasing real heights
$h_k$ and Schwartz test functions $f_k$, for $k = 0, \dots, n-1$. As $r$
decreases to $0$, the integral over configurations $x$ of the continuation of
these graded fields at the complex times $t(x_k) + \mathrm i\, r h_k$ and the
spatial positions of $x$, multiplied by the product test of the $f_k$, tends
to the vacuum expectation value, in the Wightman theory, of the smeared fields
with the labels $\iota_{d_k}(u_k)$ and the test functions $f_k$. Here
$t(x_k)$ is the time, the last coordinate, of the point $x_k$, and
$\mathrm i$ is the imaginary unit. The continuation is
also complex differentiable in the complex times, for fixed spatial positions,
on the ordered tube. At separated configurations, the correlation of a
character depends continuously on the character, and its integral against the
phase measure is the unselected correlation, while the phase measure is a
probability measure that gives positive measure to every nonempty open set of
characters. Four further conditions concern the fields: each map $\iota_d$ is
injective, every label is $\iota_d(u)$ for some graded field $(d, u)$, every
graded field is assigned to some token, and for some graded field $(d, u)$ and
some Schwartz test function $f$ the smeared field of the label $\iota_d(u)$
and $f$ is not the zero map.

The
[upstream description of the operator product expansion](../../sources/upstream-readme.md#all-orders-separated-ope)
ends with the sentence "Permutation symmetry and smoothness hold off the
collision diagonals." In the formal statement both are reconstruction
conditions, and both are required for every character and for the unselected
value: the correlations do not change when the graded fields and the points
of a separated configuration are permuted together, and they are infinitely
differentiable, in the real sense, on the open set of separated
configurations.

## The hierarchy

Besides the conditions built into its data, a continuum hierarchy is subject
to three conditions only: each field
space $F_d$ is finite-dimensional, and the space of characters is compact and
carries the Borel σ-algebra of its metric. None of the four properties is
part of the definition. In particular the Wightman theory of a hierarchy need
not satisfy the Wightman axioms, and nothing in the definition relates the
correlations, the continuation or the coefficients to the Wightman theory or
to one another.

- [Continuum hierarchy](hierarchy.md)

## Variables of the analytic continuation

Five articles define the variables at which the reconstruction conditions
evaluate the continuation, and the product tests against which they integrate
it. The
Euclidean configurations of $n$ points form $(\mathbb R^4)^n$ with the
Euclidean norm of $\mathbb R^{4n}$, in the source's words "ordered
configurations of $n$ insertion points"; this is the space
of [configurations of n points](../spacetime/point-configurations.md) of the
spacetime chapter. The complex times and the spatial positions, which the
source calls the complex time coordinates and the spatial coordinates of an
analytically continued correlation, are the plain tuples
$z \in \mathbb C^n$ and $\xi \in (\mathbb R^3)^n$. The ordered tube, "the
tube of complex times with strictly ordered imaginary parts", consists of the
$z$ with
$\operatorname{Im} z_0 < \operatorname{Im} z_1 < \dots < \operatorname{Im} z_{n-1}$.
For a real number $r$ and real heights $h_0, \dots, h_{n-1}$, the complex
shift of a configuration $x$ has the complex times
$t(x_k) + \mathrm i\, r h_k$; the source describes it as continuing "a real
configuration into ordered imaginary-time directions". The imaginary times of
$x$ are the purely imaginary numbers $\mathrm i\, t(x_k)$, and its spatial
positions are the spatial parts of its points, formed by their first three
coordinates. Finally, Schwartz test functions $f_0, \dots, f_{n-1}$ on
$\mathbb R^4$ give the product test
$x \mapsto f_0(x_0) f_1(x_1) \cdots f_{n-1}(x_{n-1})$ on configurations, "the
product test used to smear an $n$-point correlation".

- [Complex times and spatial positions](continuation-variables.md)
- [Ordered tube](ordered-tube.md)
- [Complex shift of a configuration](complex-shift.md)
- [Imaginary times and spatial positions of a configuration](imaginary-times.md)
- [Product test functions](product-tests.md)

## Reconstruction

The reconstruction conditions form one condition on a hierarchy, made of the
fifteen requirements described above; the
[four properties](../challenge/hierarchy-properties.md) of the challenge list
it second, after Wilson origin. Its article states each requirement with its
quantifiers and domains: which requirements hold for every character and for
the unselected value, which only at separated configurations, and which
concern the selected character alone.

- [Reconstruction conditions](reconstruction.md)
