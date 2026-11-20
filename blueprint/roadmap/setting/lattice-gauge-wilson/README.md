# Lattice, symmetries, gauge groups and the Wilson measure

This chapter maps the setting of the construction, the single unit of the
part on the setting in
[Armstrong's informalization](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure).
The ledger page
[Ledger of the setting: lattice, symmetries, gauge groups and the Wilson measure](../../../sources/lattice-gauge-wilson.md)
lists the declarations of the original source that the unit consists of. The unit uses
no other unit. It sets up the periodic lattices of four-dimensional space and
their sites; parallel transport, gauge transformations and the pullback of
configurations by lattice symmetries; the subdivision of a lattice into blocks
and the schedule of lattice spacings; cover numbers, a combinatorial measure of
the size of a set of sites; the gauge group in its defining unitary
representation, with its Lie algebra, colour coordinates, Casimir constant,
local logarithm, nearest-point retraction and curvature; the Haar measure; the
Wilson energy and the Wilson law, with their invariance under lattice
symmetries and gauge transformations; and the Lorentz and Poincaré groups of
Minkowski spacetime.

This version maps six key statements of the unit and the notions they use:
the sites of the periodic lattice, the separation of two sites, the gauge
group, the theorem that invariant symmetric forms on the colour space are
multiples of the standard inner product, the lower bound for the Haar mass of
small chord balls, and the lattice gauge configurations. The other
declarations of the unit are listed on the ledger and have no article. Those
that the chapter refers to are the following, described here in words.

- For a configuration $U$ of the lattice of side $M$ (defined below), the
  transport along a walk of unit steps from a site $x$ is the ordered product
  of the variables of the links it traverses: a forward step from $y$ along
  axis $i$ contributes $U(y, i)$, and a backward step from $y$ along axis $i$
  contributes $U(y - e_i, i)^{-1}$, where $e_i$ is the unit vector of axis $i$.
- A gauge transformation, a map $g : \Lambda_M \to G$, sends $U$ to the
  configuration $U^g(x, i) = g(x)\, U(x, i)\, g(x + e_i)^{-1}$.
- An affine map $x \mapsto \rho x + b$ of the lattice, with $\rho$ a signed
  permutation of the four axes, pulls a configuration back: the new variable of
  the link $(x, i)$ is the transport of $U$ along the image of that link.
- The Wilson energy of $U$ is
  $E(U) = \sum_{x \in \Lambda_M} \sum_{0 \le i < j \le 3} \big(1 - \operatorname{Re} \operatorname{tr} U_{x;ij}/(n+1)\big)$,
  where $U_{x;ij}$ is the transport around the unit square at $x$ along the
  steps $+e_i, +e_j, -e_i, -e_j$.
- The product Haar measure on configurations has one factor $h_G$, the Haar
  probability measure of the gauge group, for each link $(x, i)$. For a real
  number $\beta$, the Wilson law is the measure with density $e^{-\beta E}/Z$
  with respect to the product Haar measure, where $Z$ is the integral of
  $e^{-\beta E}$ against it.

The public statement has its own versions of several of these notions: the
matrix gauge group $(n, G, \mathfrak g)$ and its simplicity, in the articles
[Matrix gauge group](../../gauge-groups/gauge-group.md) and
[Simplicity of the gauge Lie algebra](../../gauge-groups/simple-lie-algebra.md)
of the chapter
[Compact simple matrix gauge groups](../../gauge-groups/README.md); the
periodic lattice, link configurations, Wilson action and Wilson measure in the
chapter
[Wilson lattice and its ordered continuum limit](../../wilson-lattice/README.md);
and the Lorentz transformations in the chapter
[Spacetime, Lorentz symmetry and test functions](../../spacetime/README.md).
This chapter's notions are the source's internal ones, separate declarations
from the public ones. The internal gauge group $(n, G)$ has three components
where the public one has five: it has no Lie algebra among its components,
and its Lie algebra is defined from $G$. No declaration of this unit relates
the internal notions to the public ones, and no article of this chapter
depends on the public chapters. Declarations of a unit not yet mapped do
relate them; Armstrong's outline counts them in his unit VIII.1, the assembly
of the main theorem. One sends a public gauge group $(n, G, \mathfrak g)$ to the internal gauge group
$(n, G)$, forgetting $\mathfrak g$; another proves that if the public gauge
group is simple, so is the internal one, and its proof identifies the internal
Lie algebra with $\mathfrak g$ through the exponential condition of the public
definition. The same unit proves that the public Wilson action of a
configuration equals its internal Wilson energy, and that the public Wilson
measure with Haar measure $h = h_G$ equals the internal Wilson law.

**Notation.** Axes are numbered $0, 1, 2, 3$, with time the axis $3$. A
four-component array is written $(a_0, a_1, a_2, a_3)$. A side is a positive
integer $M$, and $\Lambda_M = (\mathbb Z/M\mathbb Z)^4$ is the periodic
lattice of side $M$; sites are $x, y, z$, with coordinates $x_i$. The centred
lift of a site $x$ is $\tilde x \in \mathbb Z^4$, the torus modulus of $z$ is
$|z|_M$ and the separation of $x$ and $y$ is $|x - y|_M$. A gauge group is
$(n, G)$, with matrices of size $n+1$; $M_{n+1}(\mathbb C)$ is the space of
complex $(n+1)\times(n+1)$ matrices, elements of $G$ are $u, v$, and each is
identified with its matrix. $\mathfrak g$ is the Lie algebra of the gauge
group and $[X, Y] = XY - YX$. The real Frobenius inner product and norm are
$\langle X, Y \rangle_F = \operatorname{Re} \operatorname{tr}(X Y^*)$ and
$\|X\|_F$. The number of colours is $d = \dim_{\mathbb R} \mathfrak g$; the
colour space $\mathbb R^d$ has the standard inner product
$\langle c, c' \rangle$ and norm $|c|$. The fixed Frobenius-orthonormal basis
of $\mathfrak g$ is $T_0, \dots, T_{d-1}$, the colour matrix of $c$ is
$X_c = \sqrt{n+1} \sum_k c_k T_k$, $P_{\mathfrak g}$ is the orthogonal
projection onto $\mathfrak g$, $\Pi$ the colour projection and
$\operatorname{ad}(c)\, c'$ the colour bracket. A bilinear form on the colour
space is $B$, with scalar $\lambda$. The normalized chord is $\chi(u)$, the
Haar probability measure is $h_G$, and $D$ is the real dimension of
$M_{n+1}(\mathbb C)$. A link is $(x, i)$, a configuration is $U$ with values
$U(x, i)$, and the set of configurations of side $M$ is $\mathcal C_M$.

## The periodic lattice

The axes are the four numbers $0, 1, 2, 3$; as in the rest of the book, axes
$0, 1, 2$ are read as spatial and axis $3$ as time. For a set $R$, a
four-component array over $R$ is a map from the axes to $R$, one component
for each axis, with no condition; over an additive group, arrays are added
componentwise.

- [Axes and four-component arrays](axes-and-arrays.md)

A side is a positive integer $M$, the side $M = 1$ included. The sites of the
periodic lattice of side $M$ are the four-component arrays over the integers
modulo $M$, so the set of sites is $\Lambda_M = (\mathbb Z/M\mathbb Z)^4$,
with coordinatewise addition modulo $M$. No metric is part of the
definition; the unit proves that $\Lambda_M$ has $M^4$ sites.

- [Sites of the periodic lattice](torus-sites.md)

Distances on $\Lambda_M$ are computed from integer representatives, points
of the cover $\mathbb Z^4$. The centred
lift $\tilde x$ of a site $x$ replaces each coordinate $x_i$ by its standard
representative $w_i \in \{0, \dots, M-1\}$ when $w_i \le \lfloor M/2 \rfloor$
and by $w_i - M$ otherwise. The unit proves that $\tilde x$ is the unique
integer array that reduces to $x$ modulo $M$ and has all its coordinates in
$(-M/2, M/2]$; for even $M$ the tie $w_i = M/2$ lifts to $+M/2$.

- [Centred lift of a site](centred-lift.md)

The torus modulus $|z|_M$ of a site $z$ is the largest absolute value of a
coordinate of $\tilde z$, a natural number, and the separation of two sites
is $|x - y|_M$, the modulus of their difference. The lift is applied to the
difference $x - y$, not to $x$ and $y$ separately. The unit proves that the
separation vanishes on the diagonal, is symmetric, satisfies the triangle
inequality and is invariant under translations and signed permutations of
the axes.

- [Separation of two sites](torus-separation.md)

## Gauge groups

The internal gauge group $(n, G)$ has three components: a natural number $n$,
a subgroup $G$ of the unitary group $U(n+1)$ of complex $(n+1)\times(n+1)$
matrices, and the condition that $G$ be closed in $U(n+1)$. It has no Lie
algebra among its components, and it states no compactness, connectedness or
simplicity condition. Compactness follows from closedness, since $U(n+1)$ is
compact, and the unit proves it separately.

- [Gauge group in a unitary representation](gauge-group-in-representation.md)

The defining representation has dimension $n+1$, and its matrix space is
$M_{n+1}(\mathbb C)$. The variables of the lattice links take their values in
the group $G$ itself, and each element $u$ of $G$ is identified with its
matrix, so that products, adjoints and differences such as $u - 1$ are
computed in $M_{n+1}(\mathbb C)$.

- [Elements and matrices of a gauge group](group-elements-and-matrices.md)

The Lie algebra $\mathfrak g$ is defined from $G$ by one-parameter
exponentials: it consists of the matrices $X \in M_{n+1}(\mathbb C)$ with
$\exp(tX) \in G$ for every real $t$, and it is a real linear subspace of
$M_{n+1}(\mathbb C)$. Closure under real multiples follows by rescaling $t$.
Closure under addition is proved inside the definition by a tangent
criterion, as Armstrong's outline sketches: if a curve $t \mapsto f(t)$ in
$G$ has $f(0) = 1$ and derivative $X$ at $0$, then $\exp(tX) \in G$ for every
real $t$, because $G$ is closed. For $X, Y \in \mathfrak g$ the criterion
applies to $t \mapsto \exp(tX) \exp(tY)$, whose derivative at $0$ is $X + Y$.

- [Lie algebra of a gauge group](gauge-lie-algebra.md)

Real simplicity has the same two clauses as the simplicity of the public
statement: some two elements of $\mathfrak g$ do not commute, and every real
linear subspace of $\mathfrak g$ that contains $[X, Y]$ for all
$X \in \mathfrak g$ and all $Y$ in the subspace is $\{0\}$ or $\mathfrak g$.
Here it is a condition on the internal gauge group, stated with its Lie
algebra.

- [Real simplicity of a gauge group](real-simplicity.md)

## Colour coordinates and invariant forms

The complex $q \times q$ matrices form a real inner product space for
$\langle X, Y \rangle_F = \operatorname{Re} \operatorname{tr}(X Y^*)$, whose
norm is the Frobenius norm. The inner product carries no factor $1/q$.

- [Real Frobenius inner product](frobenius-inner-product.md)

Colours are coordinates on $\mathfrak g$. Let $d$ be the real dimension of
$\mathfrak g$, and let $T_0, \dots, T_{d-1}$ be one orthonormal basis of
$\mathfrak g$ for $\langle \cdot, \cdot \rangle_F$, fixed once and for all by
a choice. The colour frame is the real linear isomorphism
$\mathbb R^d \to \mathfrak g$, $c \mapsto X_c = \sqrt{n+1} \sum_k c_k T_k$, so
the basis is scaled by the colour scale $\sqrt{n+1}$.

- [Colour coordinates on the Lie algebra](colour-frame.md)

A matrix $A$ is sent to colours by projecting it orthogonally onto
$\mathfrak g$ and reading the projection in the colour frame:
$\Pi A$ is the colour with $X_{\Pi A} = P_{\mathfrak g} A$. The bracket of two
colours is the colour projection of the commutator of their colour matrices,
$\operatorname{ad}(c)\, c' = \Pi [X_c, X_{c'}]$, a real bilinear map.

- [Projection of matrices onto colours](colour-projection.md)
- [Bracket in colour coordinates](colour-bracket.md)

The key theorem of this section concerns a simple gauge group. Every
symmetric real bilinear form $B$ on $\mathbb R^d$ with
$B(\operatorname{ad}(c)\, c', c'') = -B(c', \operatorname{ad}(c)\, c'')$ for all
colours is a multiple $\lambda \langle \cdot, \cdot \rangle$ of the standard
inner product; the theorem says nothing about $\lambda$. The proof writes $B$
as $B(c, c') = \langle S c, c' \rangle$ for a symmetric operator $S$ on
$\mathbb R^d$. Invariance of $B$, together with the skewness of each
$\operatorname{ad}(c)$ for the standard inner product, makes $S$ commute with
every $\operatorname{ad}(c)$. Simplicity gives $d > 0$, so $S$ has a real
eigenvalue $\lambda$. Its eigenspace is nonzero and invariant under every
$\operatorname{ad}(c)$, so in the colour frame it is an ideal of
$\mathfrak g$, and simplicity makes it all of $\mathbb R^d$. Hence
$S = \lambda \cdot 1$. The unit applies the theorem to the form
$-\operatorname{tr}(\operatorname{ad}(c) \operatorname{ad}(c'))$: under
simplicity this form is a positive multiple of the standard inner product,
the multiple being the Casimir constant. The Casimir constant and that
identity are not mapped in this version.

- [Invariant symmetric forms on the colour space are multiples of the standard inner product](invariant-forms-are-scalar.md)

## Chord and Haar measure

The normalized chord of $u \in G$ is $\chi(u) = \|u - 1\|_F/\sqrt{n+1}$, with
the Frobenius norm, and the closed chord ball of radius $r$ is
$\{u \in G : \chi(u) \le r\}$.

- [Normalized chord and chord balls](chord-and-chord-balls.md)

The group $G$ carries the Borel σ-algebra of its topology. It is compact, and
its Haar probability measure $h_G$ is the left Haar measure normalized by
$h_G(G) = 1$.

- [Haar probability measure of a gauge group](haar-probability.md)

The key bound says that for $0 < r \le 1$ the chord ball of radius $r$ has
$h_G$-measure at least $(r/4)^D$, where $D = 2(n+1)^2$ is the real dimension
of the ambient matrix space $M_{n+1}(\mathbb C)$, not of $G$ or of
$\mathfrak g$; no simplicity is assumed. The proof is a packing argument in
$M_{n+1}(\mathbb C)$. Every element of $G$ has Frobenius norm $\sqrt{n+1}$,
the colour scale. Take finitely many elements of $G$ whose matrices are
pairwise more than $r\sqrt{n+1}$ apart. The Frobenius balls of radius
$r\sqrt{n+1}/2$ around them are disjoint and, as $r \le 1$, lie in the ball
of radius $2\sqrt{n+1}$ about $0$; comparing volumes in the $D$-dimensional
real space gives at most $(4/r)^D$ elements. So a maximal such set $p$
exists, and every element of $G$ lies within $r\sqrt{n+1}$ of one of its
points. The left translates $u\{\chi \le r\}$, $u \in p$, then cover $G$, and
each has the same $h_G$-measure as the ball, by left invariance. Hence
$1 \le |p|\, h_G(\{\chi \le r\})$, and the bound on $|p|$ gives the claim.

- [Haar mass of small chord balls](haar-mass-small-balls.md)

## Links and configurations

A link is a pair $(x, i)$ of a point $x$ and an axis $i$, read as the link
leaving $x$ in the positive direction of axis $i$. A link array assigns a
value to every such pair, one value per positively oriented link and none to
the reversed link.

- [Links and link arrays](links-and-link-arrays.md)

A configuration of the lattice of side $M$ is a link array over
$\mathbb Z/M\mathbb Z$ with values in $G$: a map
$U : \Lambda_M \times \{0, 1, 2, 3\} \to G$, with no condition, and
$\mathcal C_M$ is the set of all of them. The definition carries no topology
or measure. Transport, gauge transformations, the Wilson energy and the
Wilson law, described above, are built on configurations in declarations not
mapped here.

- [Lattice gauge configurations](lattice-gauge-configurations.md)
