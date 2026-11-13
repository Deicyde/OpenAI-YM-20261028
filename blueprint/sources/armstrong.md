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

## Unit V.3: reconstruction for every phase

Armstrong's unit V.3, "Reconstruction for every phase and the reconstructed
theory", is the source of the chapter
[Reconstruction for every phase](../roadmap/every-phase/README.md). Its
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
| K-V.3.1; notes, Lemma V.3.b | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| K-V.3.2; notes, Lemma V.3.u (the current jump at Euclidean times) | [The current jump at Euclidean points](../roadmap/every-phase/stress-current/euclidean-current-jump.md) |
| K-V.3.3; notes, Lemma V.3.u (the continued jump) | [Joint limit of the current jump](../roadmap/every-phase/stress-current/joint-current-jump-limit.md) |
| K-V.3.4; notes, Lemma V.3.v | [Minkowski jump identity](../roadmap/every-phase/ward-identities/minkowski-jump-identity.md) |
| K-V.3.5; notes, Lemma V.3.w | [Ward identity with arbitrary spectators](../roadmap/every-phase/ward-identities/ward-identity-schwartz-spectators.md) |
| K-V.3.6; notes, Lemma V.3.x | [The stress charge generates the transformation](../roadmap/every-phase/stress-charges/stress-charge-commutator.md) |
| K-V.3.7; Proposition V.3.y, item 8 of Proposition V.3.1 | [The stress tensor in every phase](../roadmap/every-phase/stress-charges/stress-tensor-every-phase.md) |
| K-V.3.8; Proposition V.3.1 | [Reconstruction in every phase](../roadmap/every-phase/reconstruction-every-phase.md); its items as a condition: [Completed reconstruction](../roadmap/every-phase/completed-reconstruction.md) |
| K-V.3.9; notes, Lemma V.3.e | [Continuations at strict heights: continuity and barycenter in the phase](../roadmap/every-phase/strict-height-continuity-barycenter.md) |
| K-V.3.10; Proposition V.3.o, item 6 | [Inverse-square heat decay after subtracting zero energy](../roadmap/every-phase/inverse-square-heat-decay.md) |
| K-V.3.11; notes, Lemma V.3.j, item 2 | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| K-V.3.12; Proposition V.3.n, item 5 | [Uniform low-energy bound](../roadmap/every-phase/low-energy-bound.md) |
| K-V.3.13; Proposition V.3.t, item 7 | [Irreducibility in every phase](../roadmap/every-phase/irreducibility.md), with [Weakly central bounded operators](../roadmap/every-phase/weakly-central-operators.md) and [Weak commutant with the Hilbert-space adjoint](../roadmap/every-phase/weak-commutant.md) |
| K-V.3.14; Proposition V.3.2, notes, Lemma V.3.r | [No exceptional phase: zero energy is the vacuum](../roadmap/every-phase/zero-energy-projection-vacuum.md) |
| Notation: finite sums of words, compact supports, the spectral measure of a word vector, the zero-energy and low-energy regions, the heat operator | [Finite sums of words and their vectors](../roadmap/every-phase/sums-of-words.md), [Compactly supported sums of words](../roadmap/every-phase/compactly-supported-sums.md), [Spectral measure of a finite sum of words](../roadmap/every-phase/word-spectral-measure.md), [Zero-energy and low-energy regions](../roadmap/every-phase/energy-regions.md), [Heat operators pulled back along a bounded map](../roadmap/every-phase/boundary-heat-semigroup.md) |
| Notes, §4.7, conventions: the metric, the Wick factors, the Minkowski stress labels, Killing fields and the charge | [Minkowski stress labels and the stress field](../roadmap/every-phase/stress-current/minkowski-stress-field.md), [Killing fields](../roadmap/every-phase/stress-current/killing-field.md), [Stress charge and the commutator action](../roadmap/every-phase/stress-charges/stress-charge.md) |
| Notes, Lemma V.3.u: its data and both sides | [Insertion into a slot](../roadmap/every-phase/stress-current/slot-insertion.md) (no counterpart in his text), [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-current/stress-continuation-hypotheses.md), [Spatially integrated current and its jump](../roadmap/every-phase/stress-current/integrated-current-jump.md), [Admissible base points for the current jump](../roadmap/every-phase/stress-current/jump-admissibility.md), [Euclidean value of the current jump](../roadmap/every-phase/stress-current/euclidean-jump-value.md), [Continued value of the current jump](../roadmap/every-phase/stress-current/continued-jump-value.md) |
| Notes, Lemmas V.3.v and V.3.w: their hypotheses and both sides; (T0) | [Exchange heights for every adjacent pair](../roadmap/every-phase/ward-identities/exchange-height-sequences.md), [Spacelike condition on cutoff and profile](../roadmap/every-phase/ward-identities/spacelike-cutoff-condition.md), [Test functions weighted by a Killing field](../roadmap/every-phase/ward-identities/killing-weighted-tests.md), [Tested stress insertion next to a field](../roadmap/every-phase/ward-identities/tested-current-jump.md), [Tested value of the jump](../roadmap/every-phase/ward-identities/tested-jump-value.md), [Shell identity for word expectations](../roadmap/every-phase/ward-identities/shell-identity.md) |
| Notes, Lemma V.3.x: its hypotheses and right side | [Admissible time profile](../roadmap/every-phase/stress-charges/admissible-time-profile.md), [Admissible spatial cutoff](../roadmap/every-phase/stress-charges/admissible-spatial-cutoff.md), [Infinitesimal Poincaré transformation of a field](../roadmap/every-phase/stress-charges/infinitesimal-field-transformation.md) |
| Proposition V.3.y, (T0) to (T6), as conditions | [Stress tensor of a reconstructed theory](../roadmap/every-phase/stress-charges/stress-tensor-record.md), with (T5) in [Charges generate the transformations of fields](../roadmap/every-phase/stress-charges/charge-generates-transformations.md) and (T6) in [Charges act as derivations on sums of words](../roadmap/every-phase/stress-charges/charge-acts-as-derivation.md) |

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
