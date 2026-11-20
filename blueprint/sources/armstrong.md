# Armstrong's informalization

Scott Armstrong (CNRS and Sorbonne Université; Courant Institute, New York
University) maintains *Yang–Mills informalization*, a map of OpenAI's Lean
proof and a natural-language outline built from it, in collaboration with
Martin Hairer's *humanise-yang-mills* project:
<https://github.com/scottnarmstrong/yang-mills-informalization>, read here at
commit 1a47ac9 (11 November 2026), under the Apache-2.0 license. Its outlines
were written by AI agents from the Lean and are being checked by people; it is
an informal source, not a peer-reviewed one.

This book takes from it the order and grouping of the proof (eight parts and
thirty-two units, `outline/units.md`), the plain-language readings of the
code's names (`glossary.md`), and, for each unit it maps, the unit's outline
and detailed notes. The Lean is the authority: each article states what the
cited declaration of the original source states, and where the outline and
the Lean differ the article follows the Lean, with the difference recorded on
this page.

## The main theorem

Armstrong's `statement.md` compares the public theorem with the Lean
definition by definition. The chapters from the gauge groups to
[the main theorem](../roadmap/challenge/README.md) state the same theorem
from the Lean directly; they were written from the Lean before this source
was consulted.

## Unit I.1: lattice, symmetries, gauge groups and the Wilson measure

Armstrong's unit I.1, "Lattice, symmetries, gauge groups and the Wilson
measure", is the source of the chapter
[Lattice, symmetries, gauge groups and the Wilson measure](../roadmap/setting/lattice-gauge-wilson/README.md).
Its outline is
<https://github.com/scottnarmstrong/yang-mills-informalization/blob/1a47ac9/outline/units/I-1.md>
and its detailed notes are
<https://github.com/scottnarmstrong/yang-mills-informalization/blob/1a47ac9/outline/notes/I-1.md>.
The chapter takes from them the order of the material (the periodic lattice
and its separation, the gauge group and its Lie algebra, colours and invariant
forms, the chord and the Haar measure, links and configurations), the choice
of declarations that get articles (his six key statements and the definitions
they use), the conventions of his notes (axis $3$ is time, a link joins $x$ to
$x + e_i$, a configuration assigns an element of $G$ to each link), and the
readings of the code's names in his glossary. Each article states the cited
Lean declaration itself. His key-statement summaries are, in his words,
automatically drafted summaries that the outline status does not certify.
The K-numbers, the proposition numbers and his symbols are his notation, not
Lean names: his side $\ell$ and lattice $\Lambda_\ell$ are the book's $M$ and
$\Lambda_M$, his $N$ is the book's $n + 1$, his centred lift $r_\ell(x)$ is the
book's $\tilde x$, and his Haar measure $\mu_G$ is the book's $h_G$.

| Armstrong | Articles |
| --- | --- |
| K-I.1.1; Proposition I.1.1 (the torus) | [Sites of the periodic lattice](../roadmap/setting/lattice-gauge-wilson/torus-sites.md) |
| K-I.1.2; Proposition I.1.1 (the separation) | [Separation of two sites](../roadmap/setting/lattice-gauge-wilson/torus-separation.md) |
| K-I.1.3; notes, conventions and Proposition I.1.5 | [Gauge group in a unitary representation](../roadmap/setting/lattice-gauge-wilson/gauge-group-in-representation.md) |
| K-I.1.4; notes, Proposition I.1.6(d) | [Invariant symmetric forms on the colour space are multiples of the standard inner product](../roadmap/setting/lattice-gauge-wilson/invariant-forms-are-scalar.md) |
| K-I.1.5; Proposition I.1.7 | [Haar mass of small chord balls](../roadmap/setting/lattice-gauge-wilson/haar-mass-small-balls.md) |
| K-I.1.6; notes, conventions | [Lattice gauge configurations](../roadmap/setting/lattice-gauge-wilson/lattice-gauge-configurations.md) |
| Notes, conventions: axes, links and link variables | [Axes and four-component arrays](../roadmap/setting/lattice-gauge-wilson/axes-and-arrays.md), [Links and link arrays](../roadmap/setting/lattice-gauge-wilson/links-and-link-arrays.md), [Elements and matrices of a gauge group](../roadmap/setting/lattice-gauge-wilson/group-elements-and-matrices.md) |
| Proposition I.1.1: the centred lift | [Centred lift of a site](../roadmap/setting/lattice-gauge-wilson/centred-lift.md) |
| Proposition I.1.5: the chord and the Haar measure | [Normalized chord and chord balls](../roadmap/setting/lattice-gauge-wilson/chord-and-chord-balls.md), [Haar probability measure of a gauge group](../roadmap/setting/lattice-gauge-wilson/haar-probability.md) |
| Proposition I.1.6(a) and notes, I.1.6(c): the Lie algebra and simplicity | [Lie algebra of a gauge group](../roadmap/setting/lattice-gauge-wilson/gauge-lie-algebra.md), [Real simplicity of a gauge group](../roadmap/setting/lattice-gauge-wilson/real-simplicity.md) |
| Notes, Proposition I.1.6(b): colours | [Real Frobenius inner product](../roadmap/setting/lattice-gauge-wilson/frobenius-inner-product.md), [Colour coordinates on the Lie algebra](../roadmap/setting/lattice-gauge-wilson/colour-frame.md), [Projection of matrices onto colours](../roadmap/setting/lattice-gauge-wilson/colour-projection.md), [Bracket in colour coordinates](../roadmap/setting/lattice-gauge-wilson/colour-bracket.md) |

Propositions I.1.2 to I.1.4 and I.1.8 to I.1.12, the plaquette cost of
Proposition I.1.5, the adjoint representation and the exponential map of
Proposition I.1.6(b), and parts (e) and (f) of Proposition I.1.6 (the
Casimir and slope constants) have no articles; the declarations of the unit's
files are on the [ledger](lattice-gauge-wilson.md).

### Where the outline and the Lean differ

Each difference names his file and section ("outline" is
`outline/units/I-1.md`, "notes" is `outline/notes/I-1.md`, "glossary" is
`glossary.md`) and the Lean declaration at commit 3456e5e. The articles
follow the Lean.

- **K-I.1.3 summary: compactness of the gauge group.** Outline, key
  statements, K-I.1.3, calls the gauge group "a closed compact matrix group
  together with a fixed faithful unitary representation", as the docstring of
  the Lean structure does. The Lean structure has three
  fields, the size, the subgroup and its closedness, and no compactness field,
  [`YM.Gauge`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L23);
  compactness and second countability are unnamed instances proved from
  closedness,
  [compactness](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L80)
  and
  [second countability](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L84),
  using
  [`YM.Gauge.compactGaugeU`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L61).
  Notes §1, Proposition I.1.5, states compactness and second countability as
  properties of $G$, which agrees with the Lean. The gauge-group article states
  closedness only.
- **Colour basis.** Notes §1, Proposition I.1.6(b), takes the
  $\mathrm{Ad}(G)$-invariant inner product $-\frac1N \operatorname{tr}(XY)$ on
  $\mathfrak g$ and fixes an orthonormal basis for it; outline §1,
  Proposition I.1.6, identifies $\mathfrak g$ with the colours through the
  same inner product. The unit's files define no such inner product. The Lean
  takes
  Mathlib's orthonormal basis of $\mathfrak g$ for the real Frobenius inner
  product, one fixed basis chosen by the axiom of choice, and multiplies it by
  $\sqrt{n+1}$,
  [`YM.Gauge.colorIso`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L52)
  with
  [`YM.Gauge.frobInner`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L26).
  That the colours are orthonormal for
  $-\frac1{n+1} \operatorname{Re} \operatorname{tr}(XY)$ is a theorem,
  [`YM.Gauge.trace_color`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L71),
  and the trace is real by
  [`YM.Gauge.trace_color_real`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L77).
  The articles speak of one fixed basis, not an arbitrary one.
- **The projection onto colours.** Notes §1, Proposition I.1.6(b), defines
  $\Pi$ implicitly by $X_{\Pi A} = P_{\mathfrak g} A$. The Lean defines it
  explicitly, as the orthogonal projection onto $\mathfrak g$ for the
  Frobenius inner product followed by the inverse of the colour frame,
  [`YM.Gauge.projectColor`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L96);
  the implicit characterization is a theorem,
  [`YM.Gauge.colorMat_project`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L99).
  The two agree.
- **K-I.1.4 summary.** Outline, key statements, K-I.1.4, says that on a
  simple compact Lie algebra every symmetric ad-invariant bilinear form is a
  scalar multiple of "the Killing/inner product". The theorem is about forms
  on the colour space $\mathbb R^d$, states invariance with the colour
  bracket, gives a multiple of the standard inner product of $\mathbb R^d$,
  not of the Killing form, and assumes the internal simplicity condition,
  [`YM.Gauge.invariant_scalar`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L99)
  with
  [`YM.Gauge.Simple`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L179).
  His notes (§1, Proposition I.1.6(d)) state it as the Lean does; his scalar
  $c$ is the book's $\lambda$, since the book writes $c$ for a colour.
- **K-I.1.5 summary.** Outline, key statements, K-I.1.5, bounds the Haar
  measure of "a shell of radius r in a compact group" below by $(r/4)$ to the
  dimension of the Lie algebra. The theorem's set is the closed chord ball
  $\{\chi \le r\}$ around $1$, its hypothesis is $0 < r \le 1$, its measure is
  the gauge group's Haar probability measure, and its exponent is the real
  dimension $2(n+1)^2$ of $M_{n+1}(\mathbb C)$, not $\dim \mathfrak g$,
  [`YM.Gauge.shell_ge`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Size.lean#L80)
  with
  [`YM.Gauge.shell`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Size.lean#L28).
  His Proposition I.1.7 (outline §1, exponent $2N^2$; notes §1, "not
  $\dim G$") agrees with the Lean.
- **K-I.1.2 summary.** Outline, key statements, K-I.1.2, describes the
  separation as the max-distance "computed via canonical lifts to the cover",
  and the glossary reads it as the sup-norm distance on the torus. The Lean
  separation of $x$ and $y$ is the torus modulus of $x - y$, the largest
  absolute coordinate of the centred lift of the difference, a natural number,
  [`YM.Lattice.separation`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L81)
  with
  [`YM.Lattice.pdist`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L78);
  it does not lift $x$ and $y$ separately. His Proposition I.1.1 (outline §1,
  $|x - y|_\ell = \max_i |r_\ell(x - y)_i|$) agrees with the Lean.
- **The separation as a metric.** Notes §1, Proposition I.1.1, says that the
  separation is a metric, symmetric and zero exactly when $x = y$; outline §1
  calls it "the metric". The unit's files prove $|x - x|_M = 0$, symmetry and
  the triangle inequality,
  [`YM.Lattice.separation_self`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L83),
  [`YM.Lattice.separation_comm`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L93)
  and
  [`YM.Lattice.separation_triangle`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L103),
  and no declaration in YM/Lattice, YM/Corona, YM/Space, YM/Gauge, YM/Mink or
  YM/Wilson states that $|x - y|_M = 0$ implies $x = y$. The articles call it
  the separation and state only its definition.
- **The centred lift and Proposition I.1.1.** Notes §1, Proposition I.1.1,
  defines $r_\ell(x)$ as the representative with coordinates in
  $(-\ell/2, \ell/2]$ and states with it the uniqueness of that
  representative and $|\Lambda_\ell| = \ell^4$. The Lean defines the lift
  coordinatewise by Mathlib's residue of least absolute value: a residue $v$
  is kept if $v \le \lfloor M/2 \rfloor$ and replaced by $v - M$ otherwise,
  [`YM.Lattice.lift`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L51).
  The interval, the uniqueness and the count are separate theorems,
  [`YM.Lattice.lift_centers`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L56),
  [`YM.Lattice.lift_eq_iff`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L61)
  and
  [`YM.Lattice.site_card`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L32).
- **Reduction and distances.** Outline §1 and notes §1, Proposition I.1.1,
  state that reduction does not increase distances,
  $|[y]_\ell|_\ell \le \max_i |y_i|$ for $y \in \mathbb Z^4$. The Lean states
  it coordinatewise: each coordinate of the centred lift of the reduction of
  $v \in \mathbb Z^4$ has absolute value at most $|v_i|$,
  [`YM.Lattice.Corona.lap`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L32);
  the bound on the maximum follows.
- **Glossary readings of edges and residues.** The glossary reads
  `YM.Lattice.Edge` as "a link: site together with a positive direction" and
  `YM.Lattice.Per` as "Z/nZ, one periodic axis of the lattice". The Lean edge
  is a pair of a point of an arbitrary set and an axis,
  [`YM.Lattice.Edge`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L21),
  and is a link of the lattice only inside link arrays, where the set is the
  four-component arrays,
  [`YM.Lattice.Links`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L21).
  The Lean residues are the ring of integers modulo the side, with no
  reference to axes,
  [`YM.Lattice.Per`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L18),
  and are the coordinates of each axis only in the sites,
  [`YM.Lattice.Site`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L19).
  The articles follow the Lean.

## Unit V.3: reconstruction for every phase

Armstrong's unit V.3, "Reconstruction for every phase and the reconstructed
theory", is the source of the chapter
[Reconstruction for every phase](../roadmap/phases/every-phase/README.md). Its
outline is
<https://github.com/scottnarmstrong/yang-mills-informalization/blob/1a47ac9/outline/units/V-3.md>
and its detailed notes are
<https://github.com/scottnarmstrong/yang-mills-informalization/blob/1a47ac9/outline/notes/V-3.md>.
The chapter takes from them the order of the argument (the family of
reconstructions, continuity in the phase, surjectivity of the boundary
isometry, the low-energy bound and heat decay, the vacuum at every phase,
irreducibility, the continued stress tensor and the assembly of Proposition
V.3.1), the choice of declarations that get articles (his fourteen key
statements and the definitions they use), and the readings of the code's
names in his notation table. Each article states the cited Lean declaration
itself. His key-statement summaries are, in his words, automatically drafted
summaries that the outline status does not certify. The K-numbers and the
proposition and lemma numbers below are his identifiers, not Lean names.

| Armstrong | Articles |
| --- | --- |
| K-V.3.1; notes, Lemma V.3.b | [Family of reconstructions over the phases](../roadmap/phases/every-phase/reconstruction-family.md) |
| K-V.3.2; notes, Lemma V.3.u (the current jump at Euclidean times) | [The current jump at Euclidean points](../roadmap/phases/every-phase/stress-current/euclidean-current-jump.md) |
| K-V.3.3; notes, Lemma V.3.u (the continued jump) | [Joint limit of the current jump](../roadmap/phases/every-phase/stress-current/joint-current-jump-limit.md) |
| K-V.3.4; notes, Lemma V.3.v | [Minkowski jump identity](../roadmap/phases/every-phase/ward-identities/minkowski-jump-identity.md) |
| K-V.3.5; notes, Lemma V.3.w | [Ward identity with arbitrary spectators](../roadmap/phases/every-phase/ward-identities/ward-identity-schwartz-spectators.md) |
| K-V.3.6; notes, Lemma V.3.x | [The stress charge generates the transformation](../roadmap/phases/every-phase/stress-charges/stress-charge-commutator.md) |
| K-V.3.7; Proposition V.3.y, item 8 of Proposition V.3.1 | [The stress tensor in every phase](../roadmap/phases/every-phase/stress-charges/stress-tensor-every-phase.md) |
| K-V.3.8; Proposition V.3.1 | [Reconstruction in every phase](../roadmap/phases/every-phase/reconstruction-every-phase.md); its items as a condition: [Completed reconstruction](../roadmap/phases/every-phase/completed-reconstruction.md) |
| K-V.3.9; notes, Lemma V.3.e | [Continuations at strict heights: continuity and barycenter in the phase](../roadmap/phases/every-phase/strict-height-continuity-barycenter.md) |
| K-V.3.10; Proposition V.3.o, item 6 | [Inverse-square heat decay after subtracting zero energy](../roadmap/phases/every-phase/inverse-square-heat-decay.md) |
| K-V.3.11; notes, Lemma V.3.j, item 2 | [The boundary isometry is onto](../roadmap/phases/every-phase/boundary-isometry-surjective.md) |
| K-V.3.12; Proposition V.3.n, item 5 | [Uniform low-energy bound](../roadmap/phases/every-phase/low-energy-bound.md) |
| K-V.3.13; Proposition V.3.t, item 7 | [Irreducibility in every phase](../roadmap/phases/every-phase/irreducibility.md), with [Weakly central bounded operators](../roadmap/phases/every-phase/weakly-central-operators.md) and [Weak commutant with the Hilbert-space adjoint](../roadmap/phases/every-phase/weak-commutant.md) |
| K-V.3.14; Proposition V.3.2, notes, Lemma V.3.r | [No exceptional phase: zero energy is the vacuum](../roadmap/phases/every-phase/zero-energy-projection-vacuum.md) |
| Notation: finite sums of words, compact supports, the spectral measure of a word vector, the zero-energy and low-energy regions, the heat operator | [Finite sums of words and their vectors](../roadmap/phases/every-phase/sums-of-words.md), [Compactly supported sums of words](../roadmap/phases/every-phase/compactly-supported-sums.md), [Spectral measure of a finite sum of words](../roadmap/phases/every-phase/word-spectral-measure.md), [Zero-energy and low-energy regions](../roadmap/phases/every-phase/energy-regions.md), [Heat operators pulled back along a bounded map](../roadmap/phases/every-phase/boundary-heat-semigroup.md) |
| Notes, §4.7, conventions: the metric, the Wick factors, the Minkowski stress labels, Killing fields and the charge | [Minkowski stress labels and the stress field](../roadmap/phases/every-phase/stress-current/minkowski-stress-field.md), [Killing fields](../roadmap/phases/every-phase/stress-current/killing-field.md), [Stress charge and the commutator action](../roadmap/phases/every-phase/stress-charges/stress-charge.md) |
| Notes, Lemma V.3.u: its data and both sides | [Insertion into a slot](../roadmap/phases/every-phase/stress-current/slot-insertion.md) (no counterpart in his text), [Hypotheses for continuing the stress current](../roadmap/phases/every-phase/stress-current/stress-continuation-hypotheses.md), [Spatially integrated current and its jump](../roadmap/phases/every-phase/stress-current/integrated-current-jump.md), [Admissible base points for the current jump](../roadmap/phases/every-phase/stress-current/jump-admissibility.md), [Euclidean value of the current jump](../roadmap/phases/every-phase/stress-current/euclidean-jump-value.md), [Continued value of the current jump](../roadmap/phases/every-phase/stress-current/continued-jump-value.md) |
| Notes, Lemmas V.3.v and V.3.w: their hypotheses and both sides; (T0) | [Exchange heights for every adjacent pair](../roadmap/phases/every-phase/ward-identities/exchange-height-sequences.md), [Spacelike condition on cutoff and profile](../roadmap/phases/every-phase/ward-identities/spacelike-cutoff-condition.md), [Test functions weighted by a Killing field](../roadmap/phases/every-phase/ward-identities/killing-weighted-tests.md), [Tested stress insertion next to a field](../roadmap/phases/every-phase/ward-identities/tested-current-jump.md), [Tested value of the jump](../roadmap/phases/every-phase/ward-identities/tested-jump-value.md), [Shell identity for word expectations](../roadmap/phases/every-phase/ward-identities/shell-identity.md) |
| Notes, Lemma V.3.x: its hypotheses and right side | [Admissible time profile](../roadmap/phases/every-phase/stress-charges/admissible-time-profile.md), [Admissible spatial cutoff](../roadmap/phases/every-phase/stress-charges/admissible-spatial-cutoff.md), [Infinitesimal Poincaré transformation of a field](../roadmap/phases/every-phase/stress-charges/infinitesimal-field-transformation.md) |
| Proposition V.3.y, (T0) to (T6), as conditions | [Stress tensor of a reconstructed theory](../roadmap/phases/every-phase/stress-charges/stress-tensor-record.md), with (T5) in [Charges generate the transformations of fields](../roadmap/phases/every-phase/stress-charges/charge-generates-transformations.md) and (T6) in [Charges act as derivations on sums of words](../roadmap/phases/every-phase/stress-charges/charge-acts-as-derivation.md) |

Remark V.3.3 and the other lemmas of his notes (V.3.a, V.3.c, V.3.d, V.3.f
to V.3.i, V.3.k to V.3.m, V.3.p, V.3.q and V.3.s) have no articles; their
declarations are on the [ledger](every-phase.md).

### Where the outline and the Lean differ

Each difference names his file and section ("outline" is
`outline/units/V-3.md`, "notes" is `outline/notes/V-3.md`) and the Lean
declaration at commit 3456e5e. The articles follow the Lean.

- **Surjectivity of the boundary map.** Outline §1 and notes §1, Proposition
  V.3.1 item 2, call the boundary map unitary. The Lean's completed
  reconstruction records only that it is surjective,
  [`YM.EveryPhase.Completed.into_onto`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L53);
  the isometry, the vacuum and the intertwining of translations are the
  boundary-isometry property that the family carries,
  [`YM.EveryPhase.Almanac.links`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L128).
- **Scope of the surjectivity lemma.** Notes §4.3, Lemma V.3.j, states
  surjectivity as item 2 for the boundary map of each phase. K-V.3.11 is a
  general lemma about any bounded map with the boundary-isometry property,
  for any tables, under staging hypotheses,
  [`YM.EveryPhase.onto`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L178);
  it is applied at each character of a family of reconstructions in
  [`YM.EveryPhase.reaches`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L20).
- **Data of the family.** Notes §4.1, Lemma V.3.b, lists for each phase an
  OS space with slab operators, a continuation with non-tangential boundary
  values, a theory without vacuum uniqueness and an isometry. The Lean family
  also stores the Euclidean reconstruction input and the compatibility data
  of each character, and its continuation field carries no property by
  itself: that it continues the phase table with non-tangential boundary
  values comes from the compatibility data,
  [`YM.EveryPhase.Almanac`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L117).
- **Action on labels.** Notes §1 and outline §1, Proposition V.3.1, give the
  theories the same Poincaré action on labels as the selected one. In the
  Lean the action on labels is indexed by the proper orthochronous Lorentz
  transformations, and the family equates these Lorentz actions,
  [`YM.EveryPhase.Almanac.spins`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L125).
- **Wightman conditions.** Notes §1, Proposition V.3.1 item 1 and the
  notation for a Wightman theory, list the vacuum values, the adjoint
  relation, locality, covariance, the spectrum condition, faithfulness and
  vacuum uniqueness for a unit vacuum, a dense domain spanned by word
  vectors and a strongly continuous unitary representation. The Lean's
  conditions also require that the star operation be the time-reflection
  adjoint of the table and that the action on labels descend from actions on
  the graded fields with the representation, continuity, boost, rotation and
  commutation laws,
  [`YM.EveryPhase.Completed.isTheory`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L52).
- **Heat operator.** Notes §1 (after item 6) and §6 (the notation table)
  define the heat semigroup on the Wightman space as the boundary map's
  adjoint composed with the OS semigroup and the boundary map, and equate it
  with the integral of the exponential of minus the heat time times the
  energy against the energy-momentum measure. The Lean
  defines this operator for any bounded map into any OS space of any table
  and states no semigroup law,
  [`YM.EveryPhase.bHeat`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L94);
  the Laplace identity is a separate lemma that needs the boundary-isometry
  property and the Wightman conditions without uniqueness,
  [`YM.EveryPhase.bHeat_pair`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L97).
- **Heat time and order in item 6.** Notes §1, item 6, takes a real heat
  time at least 1 and real inequalities. The Lean takes a nonnegative real at
  least 1 and states both inequalities in the order of the complex numbers,
  which makes the bounded quantity real; the content is the same,
  [`YM.EveryPhase.Completed.heat`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L59).
- **Item 9 in three parts.** Notes §1, item 9, has two parts. The Lean
  splits it into continuity of the boundary distributions,
  [`YM.EveryPhase.Completed.depends`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L67),
  the Euclidean barycenter over words of distinct points,
  [`YM.EveryPhase.Completed.at_words`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L68),
  and the barycenter of the boundary distributions, equal to those of the
  record's continuation of the unselected table,
  [`YM.EveryPhase.Completed.at_boundary`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L70).
- **K-V.3.10 summary.** Outline, key statements, K-V.3.10, speaks of the
  "vacuum-subtracted word correlations" after subtracting the full
  zero-energy projection. The theorem subtracts the full zero-energy
  projection and not the vacuum term,
  [`YM.EveryPhase.inverse_square`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decay.lean#L173);
  the vacuum-subtracted bound is another declaration,
  [`YM.EveryPhase.extends_decay`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vacuum.lean#L51).
  His own item 6 (outline §1) and Proposition V.3.o (notes §4.4) state the
  full projection, as the Lean does.
- **Every family.** Outline §1 and notes §1 state items 5 and 6 and
  Proposition V.3.2 for the theories whose existence Proposition V.3.1
  asserts. The Lean proves them for every family of reconstructions,
  [`YM.EveryPhase.light_bound`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L221),
  [`YM.EveryPhase.inverse_square`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decay.lean#L173)
  and
  [`YM.EveryPhase.all_plant`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vacuum.lean#L115).
- **Irreducibility and the vacuum.** Outline §4, step 6, says that vacuum
  uniqueness forces the commutant to be scalar. The Lean proof never uses
  the uniqueness clause of the Wightman conditions, which the family does
  not carry; it takes the large-time limit of the heat operator and
  identifies zero energy with the vacuum,
  [`YM.EveryPhase.all_plant`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vacuum.lean#L115)
  (his Proposition V.3.2), in
  [`YM.EveryPhase.commutant`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Irreducible.lean#L118).
  His notes (§4.6, Proposition V.3.t, step 4) argue the same way.
- **Finite sums of words.** Notes §1 (notation, "Words") defines a finite
  sum of words as an operator expression in the fields. The Lean's is
  formal data independent of any theory, a list of coefficients and words
  with labels in the common label space,
  [`YM.EveryPhase.SumOfWords`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L14);
  its operator is computed in each field system,
  [`YM.EveryPhase.operator`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L38).
- **Compact support.** Notes §1 and outline §6 ask every test function of
  the sum to be smooth with compact support. The Lean asks compact support
  of each Schwartz test in each entry of the list, entries with zero
  coefficient included, so the condition is on the list and not on the
  operator,
  [`YM.EveryPhase.finite`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L85).
- **Spectral measure.** Notes §1 and outline §6 define the spectral measure
  of a word vector by a formula: its value on a set is the pairing of the
  vector with the spectral projection of the set. In the Lean it is the diagonal measure that
  the projection-valued measure carries as data, tied to the projections on
  measurable sets by one of its fields,
  [`YM.EveryPhase.νletter`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L173).
- **Numbering of the axes.** Outline §6 and notes §4.7 (conventions) number
  the coordinates 1 to 4 with time the fourth, and write the time row of the
  stress and the time Wick factor with index 4. The Lean numbers the axes 0
  to 3 with time the last,
  [`YM.EveryPhase.Stress.eta`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L20)
  and
  [`YM.EveryPhase.Stress.zeta`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L22);
  the articles use index 3 for time.
- **Killing condition.** Notes §4.7 (conventions) asks that the transpose
  of the matrix times the metric plus the metric times the matrix vanish.
  The Lean asks that the transpose equal minus the conjugate of the matrix by
  the time reflection,
  [`YM.EveryPhase.Stress.Killing`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L20).
  The two agree because the metric is minus the time reflection.
- **Label action of a Killing field.** Notes §4.7 (conventions) names the
  infinitesimal label action of the matrix and gives no formula. The Lean
  defines it from the rotation generators alone, as the generator of the
  skew part minus i times the generator of the skew part of the symmetric
  part times the time reflection, and uses it in
  [`YM.EveryPhase.Stress.action`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L86),
  [`YM.EveryPhase.Stress.taskE`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L124),
  [`YM.EveryPhase.Stress.taskC`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Through.lean#L13)
  and
  [`YM.EveryPhase.Stress.receives`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L200).
- **The current jump at Euclidean times.** Notes §4.7, Lemma V.3.u, joins
  the contact identity and the jump, with currents built from the phase's
  Euclidean correlations at the real times just after and before the
  distinguished point. K-V.3.2 is the jump limit alone,
  [`YM.EveryPhase.Stress.pure_clock`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pure.lean#L43);
  the contact identity is
  [`YM.EveryPhase.Stress.euclidean_shell`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L128).
  The Lean current is the continued function of the boundary distributions
  at purely imaginary times, weighted by the complexified components of the
  Killing field, and the jump is stated for any second table and
  continuation satisfying the continuation hypotheses and the Euclidean Ward
  identities, not for one phase.
- **The continued jump.** Notes §4.7, Lemma V.3.u (sketch), and K-V.3.3
  speak of a configuration with complex exterior times. The Lean works with a
  base point (spatial positions, complex times and a real shift), adds that
  the shift stays below the spatial distance on the derivative supports of
  the cutoff and that exchange data exist at the tied heights, and takes the
  limit jointly in the base point and the parameter, with the continued
  value as the limit,
  [`YM.EveryPhase.Stress.through_jump`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Through.lean#L129),
  with
  [`YM.EveryPhase.Stress.allows`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L185)
  and
  [`YM.EveryPhase.Stress.atlases`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L73).
- **(T0).** Notes §4.7 and outline §1, Proposition V.3.y (T0), describe
  holomorphic extensions to the full forward tube, partial boundary values
  and tied heights with equal exchange germs at spacelike separation. In the
  Lean the record's first field only asserts that cutoffs and a Laplace
  family exist with the continuation hypotheses and the exchange data,
  [`YM.EveryPhase.Stress.Force.appointment`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L83).
  The exchange data have three fields, attenuable cutoffs, Fourier supports
  in the cones, and one sequence of heights per adjacent pair at which the
  two germs agree near points of the gap whose times are all zero,
  [`YM.EveryPhase.Stress.Gallery`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L167);
  agreement on the whole gap is derived afterwards.
- **Phase-free stress results.** Notes §4.7 fixes a phase in Lemmas V.3.u,
  V.3.v and V.3.x and writes the stress field with the phase's fields. The
  Lean states these results for arbitrary data: the jump identity for any
  boundary distributions under explicit hypotheses (continuation hypotheses,
  Euclidean Ward identities, exchange data),
  [`YM.EveryPhase.Stress.verdict`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L208),
  the commutator identity for any Wightman data satisfying the conditions
  without vacuum uniqueness,
  [`YM.EveryPhase.Stress.local_action`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L143),
  and the stress field for any Wightman data,
  [`YM.EveryPhase.Stress.fieldM`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L206).
  Among the stress results, phases enter only in the stress-tensor lemma,
  which holds for every family
  of reconstructions; its record takes both the limit table and the phase
  table, and does not contain the Euclidean Ward identities, which only its
  proof uses,
  [`YM.EveryPhase.Stress.force`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L94).
- **Sign of the test derivative.** Notes §4.7, Proposition V.3.y (T4) and
  Lemma V.3.x, use the derivative of the test function. The Lean uses minus
  that derivative,
  [`YM.EveryPhase.Stress.partialProbe`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L223).
  Conservation says that a sum vanishes, so the two forms are equivalent,
  [`YM.EveryPhase.Stress.Force.conserve`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L90);
  in the transformation of a field the minus sign is written once inside the
  definition instead of in front of the sum, which gives the same term.
- **Domain invariance in (T1).** Notes §4.7, Proposition V.3.y (T1), states
  that the representation maps the domain into itself. The Lean states that
  for every domain vector there is a domain vector equal to its image, an
  equivalent form,
  [`YM.EveryPhase.Stress.Force.orbital`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L84).
- **K-V.3.4 summary.** Outline, key statements, K-V.3.4, speaks of partial
  and joint distribution limits of the current jump. The theorem states an
  exact identity of tested boundary values, with no limit in the statement;
  the limits are inside its proof,
  [`YM.EveryPhase.Stress.verdict`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L208).
- **The integral of the profile.** Notes §4.7, Lemma V.3.v, writes the
  integral of the time profile as a factor of the right side. The Lean's
  tested jump value is the bracket without it,
  [`YM.EveryPhase.Stress.receives`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L200),
  and the jump identity multiplies it by the integral; the content is the
  same.
- **Classes of test functions.** Notes §4.7, Lemmas V.3.v and V.3.x, take
  smooth compactly supported functions, with a real spatial cutoff in V.3.v.
  The Lean takes complex-valued Schwartz functions with compact support, and
  asks for real values separately where needed: the same classes,
  [`YM.EveryPhase.Stress.verdict`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L208),
  [`YM.EveryPhase.Stress.Season`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L14)
  and
  [`YM.EveryPhase.Stress.Reservation`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L37).
  The set of points in the spatial cutoff's definition is arbitrary;
  compactness is a separate hypothesis where it is used.
- **Lemma V.3.w.** Notes §4.7 phrases the identity as Lemma V.3.v with a
  product test. The Lean states it as an identity of word expectations, with
  the Wick factors, for arbitrary words before and after the inserted pair,
  and repeats every hypothesis of the jump identity with integral 1,
  [`YM.EveryPhase.Stress.Schwartz_shells`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L147),
  with the identity
  [`YM.EveryPhase.Stress.shells`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L70).
- **K-V.3.6 summary.** Outline, key statements, K-V.3.6, says the spatial
  cutoff equals one near the support. The Lean asks that it equal 1 on an
  open ball whose whole exterior, at the times of the profile's support, is
  strictly spacelike to the set,
  [`YM.EveryPhase.Stress.Reservation`](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L37),
  as his Lemma V.3.x (notes §4.7) does.
