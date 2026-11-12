# The main theorem

The [upstream description of the public challenge](../../sources/upstream-readme.md#the-public-challenge)
states the challenge in two sentences:

> For each closed matrix subgroup with nonabelian simple real Lie algebra,
> choose one Wilson lattice family. For every strictly increasing sequence of
> volumes, it has a subsequence and a continuum hierarchy with the following
> properties.

The properties it then lists are Wilson origin, Wightman reconstruction, an
all-orders separated operator product expansion and a non-freeness test. The
earlier chapters define the objects these sentences speak of; this chapter
assembles them into the statement of the challenge. It says what it means for
a continuum hierarchy to have the four properties along a sequence of volume
indices, defines the joint existence statement, and states the main theorem,
which asserts it.

The statement ranges over the
[matrix gauge groups](../gauge-groups/README.md) $(n, G, \mathfrak g)$ that
are simple. Here $G$ is a closed subgroup of the unitary group $U(n+1)$,
$\mathfrak g$ consists of the complex $(n+1)\times(n+1)$ matrices whose real
one-parameter exponentials stay in $G$, and simplicity asks that
$\mathfrak g$ be nonabelian and have no real ideal other than $\{0\}$ and
itself. For such a gauge group the statement asks for a
[Wilson family](../wilson-lattice/wilson-family.md): two strictly increasing
sequences of positive integers that fix a periodic lattice for each pair of a
spacing index and a volume index, a real coupling for each pair of indices, a
Haar probability measure on $G$, a set of tokens and, for every token and
every site of each lattice, an insertion, a complex function of the
configurations of link variables. The family must be
[regular](../wilson-lattice/wilson-regularity.md): as the spacing index tends
to infinity, the ratio of its couplings to the logarithm of the inverse
lattice spacing tends to a positive slope, uniformly in the volume index, and
every insertion is continuous, is gauge invariant, and takes the same value
on any two configurations that agree on every link with both endpoints in a
finite stencil of lattice offsets, translated to its site, that depends only
on its token. On the continuum side
the statement asks for a
[continuum hierarchy](../continuum-hierarchy/README.md) over the family. It
carries a Wightman theory, graded spaces of fields, a complex-linear map from
each of them to the space of field labels of the Wightman theory, a map from
the tokens of the family to the graded fields, a compact metric space of
characters with a phase measure and a selected character, correlations for
every character and for an extra unselected value, a continuation that is a
function of complex times and spatial positions, channels and coefficients for
an operator product expansion, and a vector of grade four called the centered
trace.

What the challenge asks of the hierarchy is collected in four properties,
required along a sequence $\omega$ of volume indices, the volume order. They
are named after the four themes of the description, in its order. The
description's first theme also lists the fixed stencil of each token's
insertions and the logarithmic running of the couplings, two of the regularity
conditions above, which the statement requires of the family, not of the
hierarchy; its third theme also lists permutation symmetry and smoothness at
configurations of pairwise distinct points, which are two of the
reconstruction conditions.

1. *Wilson origin.* The family converges along $\omega$, in the sense of the
   [ordered continuum limit](../wilson-lattice/ordered-continuum-limit.md),
   to the unselected correlations of the graded fields that the hierarchy
   assigns to the tokens. So for every tuple of tokens and every smooth,
   compactly supported test function whose closed support contains only
   configurations of pairwise distinct points: the test function suits the
   volume index $\omega(k)$ for all large $k$; at every volume index that the
   test function suits, the smeared lattice moments have a limit as the
   spacing index tends to infinity; and along $\omega$ these limits tend to the
   integral of the test function against the unselected correlation.
2. *Reconstruction.* The hierarchy satisfies the
   [reconstruction conditions](../continuum-hierarchy/reconstruction.md).
   Among them, its Wightman theory satisfies the axioms W0–W3; its
   continuation reproduces the correlations of the selected character at
   ordered imaginary times and, against product test functions, has the
   vacuum expectation values of the Wightman theory as boundary values; and
   at configurations of pairwise distinct points the integral of the
   correlations of the characters against the phase measure is the
   unselected correlation. In the words of the description, "integrating the
   character correlations gives the unselected Wilson limit".
3. *Operator product expansion.* The hierarchy satisfies the
   [operator product expansion](../operator-product-expansion/README.md):
   bounds, for all sufficiently small scales, on its coefficients and on the
   remainder of the expansion truncated at every degree, with one system of
   coefficients for every truncation degree, every family of spectators, every
   character and the unselected value.
4. *Non-freeness.* The hierarchy passes the
   [trace test](../non-freeness/README.md). The smeared field of the label of
   the centered trace has vacuum expectation value zero for every Schwartz
   test function. The correlation of two copies of the centered trace in the
   selected character, at the points of the time axis with times $-r/2$ and
   $r/2$, multiplied by $r^8 \log^2(1/r)$, tends to
   $3 \dim_{\mathbb R} \mathfrak g / \pi^4$ as $r \to 0^+$, a number required
   separately to be positive. And on no interval $(0, \delta)$ with
   $\delta > 0$ does this two-point function agree with the Wick profile of a
   finite list of pairs of a complex coefficient and a track of mass-shell
   modes.

The joint existence statement puts these pieces together in a fixed order of
quantifiers. For every simple matrix gauge group there is a Wilson family for
it which is regular and such that, for every strictly increasing sequence $p$
of volume indices, there are a strictly increasing sequence $q$ and a
continuum hierarchy over the family with the four properties along the volume
order $k \mapsto p(q(k))$, a subsequence of $p$. In the words of the comment
on the formal statement, "One Wilson family per gauge group, followed by a
refinement for every requested volume sequence. All four conclusions concern a
single hierarchy on that refinement." The family, with its lattices, couplings,
Haar measure, tokens and insertions, comes once for each gauge group, before $p$;
the subsequence and the hierarchy may depend on $p$; and one hierarchy carries
all four properties. The main theorem asserts the joint existence
statement, and the original source proves it from a detailed construction;
the [coverage page](../../coverage/README.md) records which parts of that
proof this book maps so far.

## The four properties

Having the four properties is a condition on a hierarchy and a volume order,
and adds no data. The volume order is an arbitrary sequence of natural numbers
here, and only Wilson origin involves it; the joint existence statement
supplies the sequence $k \mapsto p(q(k))$.

- [The four properties of a hierarchy](hierarchy-properties.md)

## The statement

The joint existence statement is a proposition, defined without being
asserted, and the main theorem asserts it.

- [Joint existence statement](joint-existence.md)
- [The main theorem](challenge-theorem.md)
