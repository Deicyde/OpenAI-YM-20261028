# PublicWilson.lean declaration ledger

PublicWilson.lean imports PublicTheory.lean, and ChallengeSpec.lean imports it.
This page lists every name that AutoformBot's Lean source index records in the
file, 26 names: 16 keyword declarations and 10 structure fields, each under the
roadmap article that covers it, in source order, followed by the two instances
the index cannot record. Kinds and line numbers are the index's; docstrings are
quoted from the file, and "none" marks a name without one. The file is a
project-authored specification by the upstream authors; the
[Sources](README.md) page gives its provenance and the build that checked it.

## Module docstring

Line 3:

> Four-dimensional periodic Wilson lattice and its ordered continuum limit.

## Options and scopes

The file sets `autoImplicit` to false (line 4), opens a `noncomputable section`
(line 5, open to the end of the file) and the namespace `YangMills` (lines 6
to 92), opens `MeasureTheory`, `TopologicalSpace`, `Filter` and `Set` (line 7),
and opens the scopes `Topology`, `BigOperators`, `Distributions` and
`Matrix.Norms.Frobenius` (line 8). As in PublicTheory.lean, no statement writes
the norm of a matrix. The file has no section headers. The definitions from
line 50 to line 85 sit in the namespace `WilsonFamily` (lines 48 to 91), where
line 49 declares the gauge group and the Wilson family as section variables.

## Declarations

### Point configurations

Covered by [Configurations of n points](../roadmap/spacetime/point-configurations.md),
line 10.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Points` | abbrev | 10 | none |

### Periodic lattice

Covered by [Periodic lattice](../roadmap/wilson-lattice/periodic-lattice.md),
line 11.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Site` | abbrev | 11 | none |

### Link configurations

Covered by [Link configurations](../roadmap/wilson-lattice/link-configurations.md),
line 12.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Configuration` | abbrev | 12 | none |

### Wilson action

Covered by [Wilson action](../roadmap/wilson-lattice/wilson-action.md), lines
13 and 25 to 27: the index of plaquette directions at line 13 and the action
itself at line 25. The Lean calls the Wilson action `wilsonEnergy`.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Directions` | abbrev | 13 | none |
| `YangMills.wilsonEnergy` | def | 25 | none |

### Plaquette

Covered by [Plaquette](../roadmap/wilson-lattice/plaquette.md), lines 20
to 23.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.plaquette` | def | 20 | none |

### Wilson measure

Covered by [Wilson measure](../roadmap/wilson-lattice/wilson-measure.md),
lines 29 to 33. The Lean calls the Wilson measure `wilsonLaw`.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.wilsonLaw` | def | 29 | none |

### Wilson family

Covered by [Wilson family](../roadmap/wilson-lattice/wilson-family.md), lines
35 to 46.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WilsonFamily` | structure | 35 | none |
| `YangMills.WilsonFamily.period` | field | 36 | none |
| `YangMills.WilsonFamily.denominator` | field | 37 | none |
| `YangMills.WilsonFamily.periodStrict` | field | 38 | none |
| `YangMills.WilsonFamily.denominatorStrict` | field | 39 | none |
| `YangMills.WilsonFamily.beta` | field | 40 | none |
| `YangMills.WilsonFamily.haar` | field | 41 | none |
| `YangMills.WilsonFamily.probability` | field | 42 | none |
| `YangMills.WilsonFamily.invariantHaar` | field | 43 | none |
| `YangMills.WilsonFamily.Token` | field | 44 | none |
| `YangMills.WilsonFamily.insertion` | field | 45 | none |

### Lattice spacing and positions

Covered by
[Lattice spacing and positions of sites](../roadmap/wilson-lattice/lattice-spacing-and-positions.md),
lines 49 to 52.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WilsonFamily.mesh` | def | 50 | none |
| `YangMills.WilsonFamily.place` | def | 51 | none |

### Finite moments

Covered by [Finite lattice moments](../roadmap/wilson-lattice/finite-moments.md),
lines 49 and 54 to 57.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WilsonFamily.finiteMoment` | def | 54 | none |

### Separated configurations

Covered by
[Separated configurations](../roadmap/spacetime/separated-configurations.md),
lines 59 to 71.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WilsonFamily.separated` | def | 59 | none |

The proof that the set is open (lines 60 to 71) is part of the definition's
body and carries no separate proof obligation. `separated` sits in the
namespace `WilsonFamily` but uses no family; ChallengeSpec.lean calls
`WilsonFamily.separated n` with no family argument.

### Separated test functions

Covered by
[Test functions on separated configurations](../roadmap/spacetime/separated-test-functions.md),
line 73.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WilsonFamily.SeparatedTest` | abbrev | 73 | none |

`SeparatedTest n` is Mathlib's `TestFunction (separated n) ℂ ⊤`, the smooth
complex functions with compact support inside the separated configurations,
not the project's Schwartz `TestFunction`. It too uses no family despite its
namespace.

### Suitable tests

Covered by [Tests suited to a volume](../roadmap/wilson-lattice/suitable-tests.md),
lines 49 and 75 to 77.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WilsonFamily.suitable` | def | 75 | none |

### Smeared moments

Covered by [Smeared lattice moments](../roadmap/wilson-lattice/smeared-moments.md),
lines 49 and 79 to 81.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WilsonFamily.smear` | def | 79 | none |

### Ordered continuum limit

Covered by
[Ordered continuum limit](../roadmap/wilson-lattice/ordered-continuum-limit.md),
lines 49 and 83 to 90.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WilsonFamily.Converges` | def | 85 | Full mesh limit at each suitable fixed physical volume; then the infinite-volume limit along the indicated strictly increasing sequence. |

## Supporting entries

Lines 16 and 17, inside the namespace `GaugeGroup` (lines 15 to 18), declare
two instances without names, for every gauge group `g`:

| Line | Instance | Definition |
| --- | --- | --- |
| 16 | `MeasurableSpace g.image` | `borel _`: the σ-algebra generated by the open sets |
| 17 | `BorelSpace g.image` | `⟨rfl⟩`: the σ-algebra of line 16 is the Borel σ-algebra, by reflexivity |

Together they give the group of every gauge group the Borel σ-algebra of its
topology, the subspace topology it inherits from the unitary group. The Haar
measure of a Wilson family (the field `haar`, line 41), the Wilson measure
(line 29), built on the configurations from that Haar measure, and the finite
moments (line 54), integrals against the Wilson measure, all rest on this
σ-algebra. The articles [Wilson measure](../roadmap/wilson-lattice/wilson-measure.md)
and [Wilson family](../roadmap/wilson-lattice/wilson-family.md) state the
convention in prose, and neither instance has an article of its own.

Lean generates the names of unnamed instances, so the source index has no row
for them, and an article's `lean:` list cannot name them, since `check`
accepts there only names the index records. AutoformBot's format records
generated names, unnamed instances among them, as supporting entries of the
declaration ledger, which this section is.

