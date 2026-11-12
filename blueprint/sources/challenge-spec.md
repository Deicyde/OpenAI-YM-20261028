# ChallengeSpec.lean declaration ledger

ChallengeSpec.lean imports PublicWilson.lean, and Challenge.lean imports it.
This page lists every name that AutoformBot's Lean source index records in the
file, 87 names: 27 keyword declarations and 60 structure fields, each under the
roadmap article that covers it, in source order. Kinds and line numbers are the
index's; docstrings are quoted from the file, and "none" marks a name without
one (no structure field in the file has a docstring). The file is a
project-authored specification by the upstream authors; the
[Sources](README.md) page gives its provenance and the build that checked it.

## Module docstring

Lines 3 and 4:

> The joint target. All correlation terms, including every spectator in the
> OPE, are evaluations of one hierarchy. Finite lattice insertions precede
> every limit.

## Options and scopes

The file sets `autoImplicit` to false (line 5), opens a `noncomputable section`
(line 6, open to the end of the file) and the namespace `YangMills` (lines 7
to 190), opens `Function`, `Filter`, `Set`, `MeasureTheory` and
`TopologicalSpace` (line 8), and opens the scopes `Topology`, `BigOperators`,
`InnerProductSpace`, `Distributions`, `Classical`, `NNReal` and `ContDiff`
(line 9). Under the scope `ContDiff`, `∞` denotes smoothness and `ω`
analyticity; the file writes `∞` once, in the field `smooth` (line 130). The
scope `Classical` makes every proposition decidable. The declarations from
line 55 to line 181 sit in the namespace `Hierarchy` (lines 53 to 182), where
line 54 declares the gauge group, the Wilson family and a hierarchy over it as
section variables.

## Declarations

### Wilson regularity

Covered by [Regularity of a Wilson family](../roadmap/wilson-lattice/wilson-regularity.md),
lines 11 to 22.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WilsonRegularity` | structure | 12 | A fixed finite lattice stencil for each insertion works at every spacing and volume. |
| `YangMills.WilsonRegularity.running` | field | 13 | none |
| `YangMills.WilsonRegularity.continuous` | field | 15 | none |
| `YangMills.WilsonRegularity.invariant` | field | 16 | none |
| `YangMills.WilsonRegularity.localSupport` | field | 19 | none |

### Hierarchy

Covered by [Continuum hierarchy](../roadmap/continuum-hierarchy/hierarchy.md),
lines 24 to 51 and 54 to 55: the structure, then the abbreviation `Tag` at
line 55 for the pairs of a grade and a field of that grade.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy` | structure | 24 | none |
| `YangMills.Hierarchy.H` | field | 25 | none |
| `YangMills.Hierarchy.labels` | field | 26 | none |
| `YangMills.Hierarchy.theory` | field | 27 | none |
| `YangMills.Hierarchy.Field` | field | 28 | none |
| `YangMills.Hierarchy.fieldAdd` | field | 29 | none |
| `YangMills.Hierarchy.fieldSpace` | field | 30 | none |
| `YangMills.Hierarchy.fieldFinite` | field | 31 | none |
| `YangMills.Hierarchy.toLabel` | field | 32 | none |
| `YangMills.Hierarchy.project` | field | 33 | none |
| `YangMills.Hierarchy.Character` | field | 34 | none |
| `YangMills.Hierarchy.characterMetric` | field | 35 | none |
| `YangMills.Hierarchy.characterSets` | field | 36 | none |
| `YangMills.Hierarchy.characterBorel` | field | 37 | none |
| `YangMills.Hierarchy.characterCompact` | field | 38 | none |
| `YangMills.Hierarchy.phaseMeasure` | field | 39 | none |
| `YangMills.Hierarchy.selected` | field | 40 | none |
| `YangMills.Hierarchy.correlation` | field | 41 | none |
| `YangMills.Hierarchy.continuation` | field | 42 | none |
| `YangMills.Hierarchy.Channel` | field | 43 | none |
| `YangMills.Hierarchy.finiteChannels` | field | 44 | none |
| `YangMills.Hierarchy.actor` | field | 45 | none |
| `YangMills.Hierarchy.coefficient` | field | 46 | none |
| `YangMills.Hierarchy.centeredTrace` | field | 48 | none |
| `YangMills.Hierarchy.Tag` | abbrev | 55 | none |

The attribute line at lines 49 to 51 registers the eight bracketed fields as
instances: `fieldAdd`, `fieldSpace`, `fieldFinite`, `finiteChannels`,
`characterMetric`, `characterSets`, `characterBorel` and `characterCompact`. It
declares nothing new.

### Grouped correlation

Covered by
[Joint correlation of a cluster and spectators](../roadmap/operator-product-expansion/grouped-correlation.md),
lines 54 and 57 to 61.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.grouped` | def | 58 | Enumerate the union of the insertion and spectator slots once, then read the hierarchy. |

### Cluster weight

Covered by [Weight of a cluster](../roadmap/operator-product-expansion/cluster-weight.md),
lines 54 and 63.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.weight` | def | 63 | none |

### Clusters and spectators

Covered by
[Clusters and clear spectators](../roadmap/operator-product-expansion/clusters-and-spectators.md),
lines 65 to 68.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.Within` | def | 65 | none |
| `YangMills.Hierarchy.Clear` | def | 67 | none |

### Operator product expansion

Covered by
[Operator product expansion](../roadmap/operator-product-expansion/operator-product-expansion.md),
lines 54 and 70 to 80.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.OperatorProductExpansion` | structure | 70 | none |
| `YangMills.Hierarchy.OperatorProductExpansion.coefficients` | field | 71 | none |
| `YangMills.Hierarchy.OperatorProductExpansion.remainder` | field | 74 | none |

### Euclidean configurations

Covered by [Spacetime and space](../roadmap/spacetime/spacetime-coordinates.md)
(`OPEPoint`) and
[Configurations of n points](../roadmap/spacetime/point-configurations.md)
(`OPEPoints`), lines 82 to 86.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.OPEPoint` | abbrev | 83 | Four-dimensional Euclidean spacetime used by the OPE estimates. |
| `YangMills.Hierarchy.OPEPoints` | abbrev | 86 | Ordered configurations of `n` insertion points. |

### Continuation variables

Covered by
[Complex times and spatial positions](../roadmap/continuum-hierarchy/continuation-variables.md),
lines 88 to 92.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.OPEComplexTimes` | abbrev | 89 | Complex time coordinates of an analytically continued correlation. |
| `YangMills.Hierarchy.OPESpacePoints` | abbrev | 92 | Spatial coordinates of an analytically continued correlation. |

### Ordered tube

Covered by [Ordered tube](../roadmap/continuum-hierarchy/ordered-tube.md),
lines 94 to 96.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.orderedTube` | def | 95 | The tube of complex times with strictly ordered imaginary parts. |

### Complex shift

Covered by
[Complex shift of a configuration](../roadmap/continuum-hierarchy/complex-shift.md),
lines 98 to 102.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.complexShift` | def | 99 | Continue a real configuration into ordered imaginary-time directions. |

### Imaginary times

Covered by
[Imaginary times and spatial positions of a configuration](../roadmap/continuum-hierarchy/imaginary-times.md),
lines 104 to 110.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.imaginaryTimes` | def | 105 | The purely imaginary times associated with a Euclidean configuration. |
| `YangMills.Hierarchy.spatialPoints` | def | 109 | Spatial coordinates of a Euclidean configuration. |

### Product tests

Covered by [Product test functions](../roadmap/continuum-hierarchy/product-tests.md),
lines 112 to 115.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.tensorTest` | def | 113 | The product test used to smear an `n`-point correlation. |

### Reconstruction

Covered by [Reconstruction conditions](../roadmap/continuum-hierarchy/reconstruction.md),
lines 54 and 117 to 143.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.Reconstructed` | structure | 117 | none |
| `YangMills.Hierarchy.Reconstructed.axioms` | field | 118 | none |
| `YangMills.Hierarchy.Reconstructed.faithful` | field | 119 | none |
| `YangMills.Hierarchy.Reconstructed.injective` | field | 120 | none |
| `YangMills.Hierarchy.Reconstructed.acts` | field | 121 | none |
| `YangMills.Hierarchy.Reconstructed.covers` | field | 122 | none |
| `YangMills.Hierarchy.Reconstructed.represents` | field | 123 | none |
| `YangMills.Hierarchy.Reconstructed.normalized` | field | 124 | none |
| `YangMills.Hierarchy.Reconstructed.fullSupport` | field | 125 | none |
| `YangMills.Hierarchy.Reconstructed.permutation` | field | 126 | none |
| `YangMills.Hierarchy.Reconstructed.smooth` | field | 129 | none |
| `YangMills.Hierarchy.Reconstructed.characterContinuity` | field | 131 | none |
| `YangMills.Hierarchy.Reconstructed.mixture` | field | 133 | none |
| `YangMills.Hierarchy.Reconstructed.analytic` | field | 135 | none |
| `YangMills.Hierarchy.Reconstructed.root` | field | 137 | none |
| `YangMills.Hierarchy.Reconstructed.boundary` | field | 139 | none |

### Trace two point function

Covered by
[Two-point function of the centered trace](../roadmap/non-freeness/trace-two-point-function.md),
lines 54 and 145 to 149.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.timePair` | def | 146 | Two insertions on the time axis at -r/2 and r/2. |
| `YangMills.Hierarchy.traceTwo` | def | 149 | none |

### Mass shell modes

Covered by
[Mass-shell modes and their kernels](../roadmap/non-freeness/mass-shell-modes.md),
lines 151 to 161.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.Mode` | structure | 152 | Elementary mass-shell kernels, including finite differential orders. |
| `YangMills.Hierarchy.Mode.mass` | field | 153 | none |
| `YangMills.Hierarchy.Mode.spatialOrder` | field | 154 | none |
| `YangMills.Hierarchy.Mode.timeOrder` | field | 155 | none |
| `YangMills.Hierarchy.Mode.numerator` | field | 156 | none |
| `YangMills.Hierarchy.Mode.continuous` | field | 157 | none |
| `YangMills.Hierarchy.Mode.homogeneous` | field | 158 | none |
| `YangMills.Hierarchy.Mode.kernel` | def | 159 | none |

### Wick profiles

Covered by [Wick profiles](../roadmap/non-freeness/wick-profiles.md), lines
162 to 166.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.Track` | structure | 162 | none |
| `YangMills.Hierarchy.Track.n` | field | 163 | none |
| `YangMills.Hierarchy.Track.modes` | field | 164 | none |
| `YangMills.Hierarchy.wickProfile` | def | 165 | none |

### Trace test

Covered by [Trace test](../roadmap/non-freeness/trace-test.md), lines 54 and
168 to 175.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.TraceTest` | structure | 168 | none |
| `YangMills.Hierarchy.TraceTest.centered` | field | 169 | none |
| `YangMills.Hierarchy.TraceTest.amplitudePositive` | field | 172 | none |
| `YangMills.Hierarchy.TraceTest.shortDistance` | field | 173 | none |
| `YangMills.Hierarchy.TraceTest.excludes` | field | 175 | none |

### Hierarchy properties

Covered by
[The four properties of a hierarchy](../roadmap/challenge/hierarchy-properties.md),
lines 54 and 177 to 181.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Hierarchy.Properties` | structure | 177 | none |
| `YangMills.Hierarchy.Properties.wilson` | field | 178 | none |
| `YangMills.Hierarchy.Properties.reconstruction` | field | 179 | none |
| `YangMills.Hierarchy.Properties.ope` | field | 180 | none |
| `YangMills.Hierarchy.Properties.nonfree` | field | 181 | none |

### Joint existence

Covered by [Joint existence statement](../roadmap/challenge/joint-existence.md),
lines 184 to 188.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.JointExistence` | def | 186 | One Wilson family per gauge group, followed by a refinement for every requested volume sequence. All four conclusions concern a single hierarchy on that refinement. |

`JointExistence` and the theorem `jointExistence` differ only in the case of
their first letter. The theorem is in Solution.lean, so its entry is on the
[Solution.lean ledger](solution.md#the-main-theorem), not here.

## Lean-side observations

- The abbreviations with the prefix `OPE` are used only by the helpers of the
  analytic continuation and by `Reconstructed`; the operator product
  expansion (lines 70 to 80) writes `Spacetime`, although the docstring of
  `OPEPoint` speaks of the OPE estimates. `OPEPoint` and `OPEPoints` restate
  `EuclideanSpace ℝ (Fin 4)` and its `PiLp 2` powers apart from `Spacetime`
  and `Points`, and unfold to the same types. `Reconstructed` applies
  `imaginaryTimes`, `spatialPoints`, `complexShift` and `tensorTest`, which
  take configurations in `OPEPoints n`, to configurations in `Points n`; the
  build accepts this through that definitional equality.
- `Within`, `Clear`, `timePair`, `Mode` with `Mode.kernel`, `Track`,
  `wickProfile`, `orderedTube`, `complexShift`, `imaginaryTimes`,
  `spatialPoints`, `tensorTest` and the `OPE` abbreviations use no hierarchy,
  although they sit in the namespace `Hierarchy`.
- `grouped` enumerates the slots of `I ⊕ J` once, with Mathlib's
  `Fintype.equivFin`, before reading the hierarchy's correlation.
- The fields `fieldAdd` and `fieldSpace` give each graded field space a norm,
  which no condition in the closure uses.
