# Wilson lattice and its ordered continuum limit

The [upstream description of the public challenge](../../sources/upstream-readme.md#wilson-origin)
lists four properties. This chapter prepares the first, Wilson origin, which
reads:

> Finite moments integrate products of local insertions against the normalized
> exponential of the plaquette action on the given group, with product Haar
> measure. For each insertion a finite set of offsets in lattice units controls
> every measurement, at every spacing and volume. Changing links outside that
> patch leaves the insertion unchanged. The ratio of the bare action
> coefficient to the logarithm of inverse lattice spacing tends to a positive
> slope, uniformly in the volume. Separated test-function moments have the full
> mesh limit at suitable fixed volumes, then the asserted volume limit.

The chapter gives the definitions behind these sentences in four steps: the
four-dimensional periodic lattice with its link configurations and plaquettes;
the Wilson action and the Wilson measure; Wilson families, which fix the
lattice sizes, the couplings, a Haar measure and the insertions once and for
all, together with their finite moments and regularity conditions; and the
ordered continuum limit of smeared moments. Of a
[matrix gauge group](../gauge-groups/gauge-group.md) $(n, G, \mathfrak g)$,
only the group $G$, a closed subgroup of the unitary group $U(n+1)$, and the
matrix size $n+1$ enter here. The lattice axes are the four coordinate axes
$0, 1, 2, 3$ of [spacetime](../spacetime/spacetime-coordinates.md), and axis
$3$ is time.

## The periodic lattice

For a positive integer $M$, the periodic lattice of side $M$ is
$(\mathbb Z/M\mathbb Z)^4$: each site has one coordinate modulo $M$ for each
axis, sites are added coordinatewise modulo $M$, and $e_i$ is the site with
coordinate $1$ on axis $i$ and $0$ on the others. A configuration assigns an
element of $G$ to every link, a pair of a site $x$ and an axis $i$, read as
the link leaving $x$ along axis $i$. The plaquette $U_{x;ij}$ of a
configuration $U$ at a site $x$ in the directions $i$ and $j$, equal or not,
multiplies the four link variables along the path
$x \to x+e_i \to x+e_i+e_j \to x+e_j \to x$, the two links of the return path
entering through their inverses; for $i \neq j$ this path goes around the unit
square at $x$ spanned by the two axes.

- [Periodic lattice](periodic-lattice.md)
- [Link configurations](link-configurations.md)
- [Plaquette](plaquette.md)

## Wilson action and Wilson measure

The Wilson action of a configuration $U$ sums, over all sites $x$ and all
pairs of axes $i < j$, one minus the real part of the trace of the plaquette
over the matrix size, $1 - \operatorname{Re}\operatorname{tr} U_{x;ij}/(n+1)$;
it contains no coupling constant. The Wilson measure,
for a real coupling $\beta$ and a measure $h$ on $G$, has density
$e^{-\beta S}$ with respect to the product of one copy of $h$ per link,
divided by the total integral of that density. This is the description's
"normalized exponential of the plaquette action on the given group, with
product Haar measure" once $h$ is the measure of a Wilson family, which is a
Haar probability measure.

- [Wilson action](wilson-action.md)
- [Wilson measure](wilson-measure.md)

## Wilson families

A Wilson family fixes all the lattice data at once. Two strictly increasing
sequences of positive integers, side lengths $L_p$ and denominators $m_N$,
give for each pair of indices $(N, p)$ the periodic lattice of side $L_p m_N$.
Its spacing is $a_N = 1/m_N$, and its sites are placed in $\mathbb R^4$ by
multiplying by $a_N$ the integer representatives of their coordinates in
$(-L_p m_N/2, L_p m_N/2]$, so that every position lies in the half-open box
$(-L_p/2, L_p/2]^4$ of side $L_p$. Thus $N$ indexes the spacing and $p$ the
volume, independently of each other.
The family also fixes a real coupling $\beta_{N,p}$ for each pair of indices, a
Haar probability measure $h$ on $G$, a set of tokens, and, for every token and
every site of each lattice, an insertion: a complex function of the
configurations on that lattice. A finite moment integrates a product of
insertions against the Wilson measure with coupling $\beta_{N,p}$ and
measure $h$.

Regularity of a family makes the three middle sentences of the description
precise, and adds two conditions the description does not mention. The
coupling $\beta_{N,p}$ divided by the logarithm of the inverse spacing tends to
a positive slope as $N \to \infty$, uniformly in $p$. Each token has one
finite stencil of lattice offsets, the same at every spacing, volume and site,
such that its insertion at a site $x$ takes the same value on any two
configurations that agree on every link with both endpoints in the stencil
translated to $x$. In addition, every insertion is continuous and is invariant
under every gauge transformation, which may assign an arbitrary element of $G$
to each site.

- [Wilson family](wilson-family.md)
- [Lattice spacing and positions of sites](lattice-spacing-and-positions.md)
- [Finite lattice moments](finite-moments.md)
- [Regularity of a Wilson family](wilson-regularity.md)

## The ordered continuum limit

Lattice moments are compared with functions of $n$ points of $\mathbb R^4$
(this $n$ counts points and is unrelated to the matrix size $n+1$) through
test functions: smooth, compactly supported complex functions on
$(\mathbb R^4)^n$ whose closed support contains only configurations of
pairwise distinct points. Such a test function suits the volume index $p$
when every point of every configuration in its closed support lies in the open
box $(-L_p/2, L_p/2)^4$. The smeared moment is a Riemann sum: $a_N^{4n}$ times
the sum, over all $n$-tuples of sites, of the test function at the positions
of the sites times the finite moment at those sites. The family converges
along a sequence $\omega$ of volume indices to prescribed functions, one function
of $n$ points for each $n$ and each tuple $v$ of $n$ tokens, when, for every
$n$, every such $v$ and every test function $t$ of $n$ points, two
requirements hold: $t$ suits the volume index $\omega(k)$ for all sufficiently
large $k$; and there are complex numbers $R_p$, one for each volume index $p$,
such that at every volume index that $t$ suits, the smeared moments of $v$
against $t$ tend to $R_p$ as $N \to \infty$, while $R_{\omega(k)}$ tends, as
$k \to \infty$, to the integral of $t$ against the function prescribed for
$v$. The source describes this limit in one line: "Full mesh limit at each
suitable fixed physical volume; then the infinite-volume limit along the
indicated strictly increasing sequence." The definition itself accepts any
sequence $\omega$;
[the challenge](../challenge/README.md) applies it along a subsequence of an
arbitrary strictly increasing sequence of volume indices, with the prescribed
functions read from a continuum hierarchy.

- [Tests suited to a volume](suitable-tests.md)
- [Smeared lattice moments](smeared-moments.md)
- [Ordered continuum limit](ordered-continuum-limit.md)
