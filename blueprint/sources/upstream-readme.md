# Upstream description of the public challenge

This page quotes the section "The public challenge" (lines 5 to 16) of the
[README.md][readme] of [yang-mills-group/OpenAI-YM-20261028][repo] at commit
3456e5e75cf8d4cd558955a5c7638fba2d68f464, and one paragraph (line 26) from the
section after it. The README states the project's license as Apache-2.0 (its
line 3); this repository keeps upstream's LICENSE and NOTICE, and the
quotations are reproduced under that license. The README is the upstream
authors' informal description of their challenge: a project-authored
specification, not a peer-reviewed source. Where it and the Lean differ, the
Lean statements are authoritative; this page only locates and summarizes.
Quotations keep the README's wording and its links, which point to files of the
upstream repository at the same commit.

## The public challenge

Line 7:

> [YangMills.jointExistence][solution] proves [JointExistence][challengespec].
> The reference [Challenge.lean][challenge] has a Mathlib-only import closure.
> Its starting point is an earlier challenge at revision
> eea94292e31734d46498be7836d7e8fa50ca8cd2.

Line 9:

> For each closed matrix subgroup with nonabelian simple real Lie algebra,
> choose one Wilson lattice family. For every strictly increasing sequence of
> volumes, it has a subsequence and a continuum hierarchy with the following
> properties.

[The main theorem](../roadmap/challenge/README.md) chapter states this claim.
[The main theorem](../roadmap/challenge/challenge-theorem.md) asserts the
[joint existence statement](../roadmap/challenge/joint-existence.md), and
Solution.lean proves it (see the [Solution.lean ledger](solution.md#the-main-theorem)).
Challenge.lean restates it with the proof `sorry` for comparison; this
project leaves that file out of its checkout, as the [Sources](README.md)
page records. The gauge groups of line 9 are the
[matrix gauge groups](../roadmap/gauge-groups/gauge-group.md) whose Lie algebra
is [simple](../roadmap/gauge-groups/simple-lie-algebra.md); the family is a
[Wilson family](../roadmap/wilson-lattice/wilson-family.md), required in the
Lean to be [regular](../roadmap/wilson-lattice/wilson-regularity.md) before any
sequence is chosen; the sequence of volumes is a strictly increasing sequence
of indices of the family's periods; and the subsequence and hierarchy are a
strictly increasing reindexing and a
[continuum hierarchy](../roadmap/continuum-hierarchy/hierarchy.md) with
[the four properties](../roadmap/challenge/hierarchy-properties.md) along the
reindexed sequence. The four bullets below are those properties, except that
the regularity conditions of the first bullet belong to the family.

## Wilson origin

Line 11:

> - **Wilson origin.** Finite moments integrate products of local insertions
>   against the normalized exponential of the plaquette action on the given
>   group, with product Haar measure. For each insertion a finite set of
>   offsets in lattice units controls every measurement, at every spacing and
>   volume. Changing links outside that patch leaves the insertion unchanged.
>   The ratio of the bare action coefficient to the logarithm of inverse
>   lattice spacing tends to a positive slope, uniformly in the volume.
>   Separated test-function moments have the full mesh limit at suitable fixed
>   volumes, then the asserted volume limit.
>   [Lattice and limits][publicwilson] · [Wilson bridge][wilsonbridge]

Sentence by sentence:

1. The [finite lattice moments](../roadmap/wilson-lattice/finite-moments.md)
   integrate products of a [Wilson family](../roadmap/wilson-lattice/wilson-family.md)'s
   insertions against the [Wilson measure](../roadmap/wilson-lattice/wilson-measure.md),
   whose density is $e^{-\beta S}$ divided by its integral, for the coupling
   $\beta$ and the [Wilson action](../roadmap/wilson-lattice/wilson-action.md)
   $S$, a sum over [plaquettes](../roadmap/wilson-lattice/plaquette.md), with
   respect to the product, over the
   [link configurations](../roadmap/wilson-lattice/link-configurations.md), of
   the family's Haar probability measure.
2. The local support condition of
   [regularity](../roadmap/wilson-lattice/wilson-regularity.md) gives each
   insertion one finite set of integer offsets, the same at every spacing and
   volume.
3. The same condition: two configurations that agree on the links with both
   ends in the shifted set give the insertion the same value.
4. The running condition of
   [regularity](../roadmap/wilson-lattice/wilson-regularity.md): the coupling
   divided by the logarithm of the inverse
   [lattice spacing](../roadmap/wilson-lattice/lattice-spacing-and-positions.md)
   tends to a positive slope, uniformly in the volume index.
5. The [ordered continuum limit](../roadmap/wilson-lattice/ordered-continuum-limit.md)
   of the [smeared lattice moments](../roadmap/wilson-lattice/smeared-moments.md)
   of [test functions on separated configurations](../roadmap/spacetime/separated-test-functions.md):
   first the limit as the spacing shrinks, at each volume
   [suited](../roadmap/wilson-lattice/suitable-tests.md) to the test
   function, then the limit along the volume order.

The Lean also requires every insertion to be continuous and gauge invariant
(the continuity and invariance conditions of
[regularity](../roadmap/wilson-lattice/wilson-regularity.md)), which the
bullet does not mention. Of its two links, PublicWilson.lean is inside the
boundary ([ledger](public-wilson.md)) and WilsonBridge.lean outside.

## Wightman reconstruction

Line 12:

> - **Wightman reconstruction.** The selected phase has a normalized cyclic
>   vacuum, faithful tempered fields on a common dense domain, positive energy,
>   a unique translation-invariant vacuum up to scalar, covariance and
>   spacelike locality. The symmetry coordinates cover every proper
>   orthochronous affine Poincaré transformation and determine the inverse
>   pullback on test functions. Analytic continuation recovers the selected
>   Euclidean hierarchy at ordered imaginary times and its Wightman vacuum
>   moments on product tests. Integrating the character correlations gives the
>   unselected Wilson limit. The character measure has full support and the
>   separated correlations vary continuously with the character.
>   [W0–W3][publictheory] · [Reconstruction bridge][hierarchybridge]

Sentence by sentence:

1. The [reconstruction conditions](../roadmap/continuum-hierarchy/reconstruction.md)
   require the hierarchy's Wightman theory to satisfy
   [the Wightman axioms](../roadmap/wightman/wightman-axioms.md) and its
   field system to be [faithful](../roadmap/wightman/faithful-fields.md). The
   normalized and cyclic vacuum, the dense common domain and temperedness are
   the [domain axioms](../roadmap/wightman/domain-axioms.md) inside
   [axiom W1](../roadmap/wightman/axiom-w1.md); positive energy and the unique
   invariant vacuum are in [axiom W0](../roadmap/wightman/axiom-w0.md);
   covariance is [axiom W2](../roadmap/wightman/axiom-w2.md); spacelike
   locality is [axiom W3](../roadmap/wightman/axiom-w3.md). In the Lean these
   conditions concern the hierarchy's one Wightman theory; the selected
   character enters through the root condition of sentence 3.
2. The [Poincaré action](../roadmap/wightman/poincare-action.md) in the data
   of every [Wightman theory](../roadmap/wightman/wightman-theory.md): a
   homeomorphism from its symmetry type onto the
   [Poincaré coordinates](../roadmap/spacetime/lorentz-and-poincare.md), with
   the pullback of test functions fixed by the affine action.
3. The analyticity, root and boundary conditions of the reconstruction
   conditions: the continuation is analytic on the
   [ordered tube](../roadmap/continuum-hierarchy/ordered-tube.md); at
   [imaginary times](../roadmap/continuum-hierarchy/imaginary-times.md) of a
   time-ordered configuration it equals the correlation of the selected
   character; and along the
   [complex shift](../roadmap/continuum-hierarchy/complex-shift.md), against
   [product test functions](../roadmap/continuum-hierarchy/product-tests.md),
   it tends to the theory's
   [vacuum expectation values](../roadmap/wightman/vacuum-expectation-values.md).
4. The mixture condition of the reconstruction conditions: integrating the correlations of every character
   against the phase measure gives the unselected correlation, the one that
   [the four properties](../roadmap/challenge/hierarchy-properties.md) compare
   with the Wilson limit.
5. The full support and character continuity conditions of the
   reconstruction conditions; their normalization condition makes the phase
   measure a probability measure.

Of the bullet's two links, PublicTheory.lean is inside the boundary
([ledger](public-theory.md)) and HierarchyBridge.lean outside.

## All-orders separated OPE

Line 13:

> - **All-orders separated OPE.** For each finite cluster and collection of
>   separated spectators, use a single system of coefficients at every
>   truncation degree and in every phase. Both the full word and each term with
>   the cluster replaced by a local insertion are reads of the same hierarchy.
>   The bounds are uniform at all sufficiently small radii for the specified
>   cluster size and separation constants. Permutation symmetry and smoothness
>   hold off the collision diagonals.
>   [Public estimates][challengespec] · [Derivation of the compact-set bounds][compactcheck]

Sentence by sentence:

1. The [operator product expansion](../roadmap/operator-product-expansion/operator-product-expansion.md):
   its coefficients are one function, part of the
   [continuum hierarchy](../roadmap/continuum-hierarchy/hierarchy.md), used for
   every truncation degree and every phase, with
   [clusters and clear spectators](../roadmap/operator-product-expansion/clusters-and-spectators.md).
2. The [joint correlation of a cluster and spectators](../roadmap/operator-product-expansion/grouped-correlation.md),
   read from the hierarchy for the full word and for each term.
3. Both bounds hold for all sufficiently small radii, for fixed size and
   separation constants, uniformly over the configurations those constants
   allow; the [weight of a cluster](../roadmap/operator-product-expansion/cluster-weight.md)
   sets their exponents.
4. In the Lean, permutation symmetry and smoothness are among the
   [reconstruction conditions](../roadmap/continuum-hierarchy/reconstruction.md),
   stated on [separated configurations](../roadmap/spacetime/separated-configurations.md),
   and are not part of the expansion.

Of the bullet's two links, ChallengeSpec.lean is inside the boundary
([ledger](challenge-spec.md)) and verification/CompactCheck.lean outside.

## Non-freeness test

Line 14:

> - **Non-freeness test.** A centered grade-four field has a two-point
>   function with a positive short-distance coefficient of three times the real
>   Lie-algebra dimension divided by π⁴, after multiplication by r⁸ log²(1/r).
>   No finite sum of the specified mass-shell Wick profiles agrees with it at
>   all sufficiently small radii. The detailed theorem identifies this field as
>   the physical centered stress trace and supplies the distributional Wick and
>   Maxwell tests. [Trace bridge][tracebridge]

Sentence by sentence:

1. The [trace test](../roadmap/non-freeness/trace-test.md): the hierarchy's
   centered trace, a field of grade four, has vacuum expectation zero when
   smeared with any test function, and its
   [two-point function](../roadmap/non-freeness/trace-two-point-function.md)
   has the stated short-distance limit, whose coefficient the test requires
   to be positive.
2. The exclusion condition of the [trace test](../roadmap/non-freeness/trace-test.md),
   for every finite sum of [Wick profiles](../roadmap/non-freeness/wick-profiles.md)
   built from [mass-shell modes](../roadmap/non-freeness/mass-shell-modes.md).
3. Outside the boundary: no declaration of the closure identifies the field
   with a stress trace or states the Wick and Maxwell tests of the detailed
   theorem.

The bullet's one link, TraceBridge.lean, is outside the boundary.

## Scope remark

Line 26, in the README's next section, "The detailed construction theorem"
(heading at line 18):

> The volume limit allows refinement. The Wightman spectrum condition and
> uniqueness of the vacuum are the spectral conclusions in the public
> challenge. A positive mass gap, general exclusion of continuous-mass
> generalized free fields and all-orders MS-bar matching are outside its
> scope.

The remark is recorded for context; no article relies on it.

## Files this version does not map

The section links to six files this version maps at most in part: Solution.lean (line 7),
WilsonBridge.lean (line 11), HierarchyBridge.lean (line 12),
verification/CompactCheck.lean (line 13), TraceBridge.lean (line 14) and
ConcreteSU2.lean (line 16). Line 16 reads:

> [The SU(2) specialization][concretesu2] uses the defining representation and
> the included proof of simplicity.

Line 7 also names the earlier challenge at revision
eea94292e31734d46498be7836d7e8fa50ca8cd2, which PublicTheory.lean's module
docstring names too. That earlier challenge is not part of this book. Of the upstream
repository beyond the files of the public statement, this version maps the
main theorem in Solution.lean and the modules of YM/EveryPhase (Armstrong's
unit V.3); the other top-level Lean files (Construction.lean, ContactSpec.lean,
ContactBridge.lean, PublicView.lean, Verify.lean, VerifyJoint.lean and the
files above), the rest of the 9,457 modules under YM/ and the verification/
directory come later, unit by unit, as the
[coverage page](../coverage/README.md) records. The section's other links, to Challenge.lean,
ChallengeSpec.lean, PublicWilson.lean and PublicTheory.lean, point to the four
files of the closure, whose ledgers are listed on the [Sources](README.md)
page.

[repo]: https://github.com/yang-mills-group/OpenAI-YM-20261028
[readme]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/README.md
[solution]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/Solution.lean
[challengespec]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/ChallengeSpec.lean
[challenge]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/Challenge.lean
[publicwilson]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/PublicWilson.lean
[wilsonbridge]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/WilsonBridge.lean
[publictheory]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/PublicTheory.lean
[hierarchybridge]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/HierarchyBridge.lean
[compactcheck]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/verification/CompactCheck.lean
[tracebridge]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/TraceBridge.lean
[concretesu2]: https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/ConcreteSU2.lean
