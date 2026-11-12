# PublicTheory.lean declaration ledger

PublicTheory.lean is the first file of the closure: it imports Mathlib only,
and PublicWilson.lean imports it. This page lists every name that AutoformBot's
Lean source index records in the file, 110 names: 37 keyword declarations and
73 structure fields, each under the roadmap article that covers it, in source
order. Kinds and line numbers are the index's; docstrings are quoted from the
file, and "none" marks a name without one (no structure field in the file has a
docstring). The file is a project-authored specification by the upstream
authors; the [Sources](README.md) page gives its provenance and the build that
checked it.

## Module docstring

Lines 3 to 6:

> Public gauge and Wightman definitions adapted from an earlier challenge,
> commit eea94292e31734d46498be7836d7e8fa50ca8cd2. The symmetry coordinates
> cover every proper orthochronous Lorentz transformation and translation.
> Their affine action fixes the transformation of test functions.

The earlier challenge lies outside this book's boundary, as the
[upstream description](upstream-readme.md#outside-the-boundary) records.

## Options and scopes

The file sets `autoImplicit` to false (line 7), opens a `noncomputable section`
(line 9, closed at line 325) and the namespace `YangMills` (lines 11 to 323),
opens `MeasureTheory`, `Set` and `Function` (line 13), and opens the scopes
`Topology`, `InnerProductSpace` and `Matrix.Norms.Frobenius` (line 14). The
last scope makes Mathlib's Frobenius norm on matrices available; no statement
in the file writes the norm of a matrix, and the scope changes no topology on
matrices (see the [Lean-side notes](lean-notes.md#mathlib-notions)).

Attribute lines that register structure fields as instances (lines 85 to 87,
101 and 102, 204, and 248 to 250) declare nothing new, so they have no rows of
their own; each is noted under the article whose fields it registers.

## Compact simple matrix gauge groups

The file marks this section with a header at line 16.

### Gauge group

Covered by [Matrix gauge group](../roadmap/gauge-groups/gauge-group.md), lines
18 to 33.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.UnitaryRepresentation` | abbrev | 20 | The fixed faithful unitary representation used to describe a gauge group. |
| `YangMills.GaugeGroup` | structure | 25 | A compact matrix gauge group together with its one-parameter Lie algebra. The last field prevents the Lie algebra from being arbitrary: it consists exactly of the matrices whose exponentials stay in the group. |
| `YangMills.GaugeGroup.n` | field | 26 | none |
| `YangMills.GaugeGroup.image` | field | 27 | none |
| `YangMills.GaugeGroup.imageClosed` | field | 28 | none |
| `YangMills.GaugeGroup.lieAlgebra` | field | 29 | none |
| `YangMills.GaugeGroup.generates` | field | 30 | none |

### Simple Lie algebra

Covered by
[Simplicity of the gauge Lie algebra](../roadmap/gauge-groups/simple-lie-algebra.md),
lines 37 to 45.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.GaugeGroup.IsSimple` | def | 39 | Real simplicity of the Lie algebra, including the nonabelian condition. |

## Spacetime and test functions

The file marks this section with a header at line 49.

### Spacetime coordinates

Covered by [Spacetime and space](../roadmap/spacetime/spacetime-coordinates.md),
lines 51 to 60.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.Axis` | abbrev | 51 | none |
| `YangMills.SpaceAxis` | abbrev | 52 | none |
| `YangMills.timeAxis` | abbrev | 53 | none |
| `YangMills.Spacetime` | abbrev | 54 | none |
| `YangMills.Space` | abbrev | 55 | none |
| `YangMills.time` | def | 57 | none |
| `YangMills.spatial` | def | 59 | none |

### Forward light cone

Covered by [Closed forward light cone](../roadmap/spacetime/forward-light-cone.md),
lines 62 to 64.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.forwardCone` | def | 64 | The closed forward light cone in the convention where time is the final coordinate. |

### Minkowski square

Covered by [Minkowski square](../roadmap/spacetime/minkowski-square.md), line 66.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.minkowskiSquare` | def | 66 | none |

### Spacelike vectors

Covered by [Spacelike vectors](../roadmap/spacetime/spacelike-vectors.md),
line 68.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.spacelike` | def | 68 | none |

### Schwartz test functions

Covered by
[Schwartz test functions](../roadmap/spacetime/schwartz-test-functions.md),
line 70.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.TestFunction` | abbrev | 70 | none |

The project's `YangMills.TestFunction` is Mathlib's Schwartz space
`SchwartzMap Spacetime ℂ`. Mathlib's own `TestFunction` is a different space,
of smooth functions with compact support, which PublicWilson.lean uses for
separated configurations.

### Conjugate test function

Covered by
[Complex conjugate of a test function](../roadmap/spacetime/conjugate-test-function.md),
lines 72 to 74.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.conjugateTest` | def | 73 | Pointwise complex conjugation of a Schwartz test function. |

`conjugateTest` is a real-linear continuous map (`→L[ℝ]`): Mathlib's
`SchwartzMap.postcompCLM` applied to complex conjugation, `Complex.conjCLE`,
taken as a real-linear map.

## Basic quantum-field structures

The file marks this section with a header at line 76.

### Hilbert space

Covered by [Hilbert space and bounded operators](../roadmap/wightman/hilbert-space.md),
lines 78 to 93.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.HilbertSpace` | structure | 79 | A bundled complex Hilbert space. |
| `YangMills.HilbertSpace.carrier` | field | 80 | none |
| `YangMills.HilbertSpace.normedAddCommGroup` | field | 81 | none |
| `YangMills.HilbertSpace.innerProductSpace` | field | 82 | none |
| `YangMills.HilbertSpace.completeSpace` | field | 83 | none |
| `YangMills.HilbertSpace.Operator` | abbrev | 91 | none |

Lines 85 to 87 register the fields `normedAddCommGroup`, `innerProductSpace`
and `completeSpace` as instances.

### Field labels

Covered by [Field labels](../roadmap/wightman/field-labels.md), lines 95
to 102.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.FieldLabels` | structure | 96 | A bundled complex vector space of field labels. |
| `YangMills.FieldLabels.carrier` | field | 97 | none |
| `YangMills.FieldLabels.addCommGroup` | field | 98 | none |
| `YangMills.FieldLabels.module` | field | 99 | none |

Lines 101 and 102 register the fields `addCommGroup` and `module` as
instances.

### Field system

Covered by [Field system](../roadmap/wightman/field-system.md), lines 104
to 109.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.FieldSystem` | structure | 105 | Operator-valued tempered fields on one common invariant domain. |
| `YangMills.FieldSystem.domain` | field | 106 | none |
| `YangMills.FieldSystem.vacuum` | field | 107 | none |
| `YangMills.FieldSystem.field` | field | 108 | none |

The definitions from line 115 to line 161 sit in the namespace `FieldSystem`
(lines 111 to 163), where line 113 declares the Hilbert space and the label
space as section variables.

### Field vectors

Covered by [Vectors generated from the vacuum](../roadmap/wightman/field-vectors.md),
lines 113 and 115 to 118.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.FieldSystem.vector` | def | 115 | none |

### Vacuum expectation values

Covered by
[Vacuum expectation values](../roadmap/wightman/vacuum-expectation-values.md),
lines 113 and 120 to 124.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.FieldSystem.vacuumExpectation` | def | 121 | The vacuum expectation of an ordered product of smeared fields. |

### Domain axioms

Covered by [Domain axioms](../roadmap/wightman/domain-axioms.md), lines 113
and 126 to 133.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.FieldSystem.DomainAxioms` | structure | 127 | W1's common-domain, temperedness, and cyclic-vacuum requirements. |
| `YangMills.FieldSystem.DomainAxioms.normalizedVacuum` | field | 128 | none |
| `YangMills.FieldSystem.DomainAxioms.denseDomain` | field | 129 | none |
| `YangMills.FieldSystem.DomainAxioms.cyclicVacuum` | field | 130 | none |
| `YangMills.FieldSystem.DomainAxioms.tempered` | field | 132 | none |

### Adjoint axiom

Covered by [Adjoint axiom](../roadmap/wightman/adjoint-axiom.md), lines 113
and 135 to 141.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.FieldSystem.AdjointAxiom` | def | 136 | The smeared adjoint identity on the common domain. |

### Spacelike separated tests

Covered by
[Spacelike separated Schwartz test functions](../roadmap/spacetime/spacelike-separated-tests.md),
lines 143 to 146.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.FieldSystem.SpacelikeSeparated` | def | 145 | Two test functions are causally disjoint when every difference of points in their supports is spacelike. |

`SpacelikeSeparated` sits in the namespace `FieldSystem` but uses no field
system: its statement mentions neither a field system nor the section
variables of line 113, and relates two Schwartz test functions only.

### Local commutativity

Covered by [Local commutativity](../roadmap/wightman/local-commutativity.md),
lines 113 and 148 to 156.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.FieldSystem.LocalCommutativity` | def | 149 | W3's local commutativity condition. |

### Faithful fields

Covered by [Faithful field system](../roadmap/wightman/faithful-fields.md),
lines 113 and 158 to 161.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.FieldSystem.Faithful` | def | 159 | Each nonzero label has a nonzero smeared field operator. |

## Translations, spectrum, and Poincaré covariance

The file marks this section with a header at line 165.

### Translation representation

Covered by
[Translation representation](../roadmap/wightman/translation-representation.md),
lines 167 to 177.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.TranslationAction` | structure | 169 | A strongly continuous unitary representation of spacetime translations. |
| `YangMills.TranslationAction.operator` | field | 170 | none |
| `YangMills.TranslationAction.identity` | field | 171 | none |
| `YangMills.TranslationAction.add` | field | 172 | none |
| `YangMills.TranslationAction.unitary` | field | 174 | none |
| `YangMills.TranslationAction.stronglyContinuous` | field | 176 | none |

The field named `unitary` (line 174) asserts only that each operator preserves
norms; no field asserts that the operators are onto.

### Energy momentum measure

Covered by
[Energy–momentum measure](../roadmap/wightman/energy-momentum-measure.md),
lines 179 to 206.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.EnergyMomentumMeasure` | structure | 180 | A projection-valued joint energy–momentum measure. |
| `YangMills.EnergyMomentumMeasure.projection` | field | 181 | none |
| `YangMills.EnergyMomentumMeasure.empty` | field | 182 | none |
| `YangMills.EnergyMomentumMeasure.univ` | field | 183 | none |
| `YangMills.EnergyMomentumMeasure.intersection` | field | 184 | none |
| `YangMills.EnergyMomentumMeasure.selfAdjoint` | field | 187 | none |
| `YangMills.EnergyMomentumMeasure.countablyAdditive` | field | 190 | none |
| `YangMills.EnergyMomentumMeasure.diagonal` | field | 195 | none |
| `YangMills.EnergyMomentumMeasure.finite` | field | 196 | none |
| `YangMills.EnergyMomentumMeasure.diagonalIdentity` | field | 197 | none |

Line 204, inside the namespace `EnergyMomentumMeasure` (lines 202 to 206),
registers the field `finite` as an instance.

### Lorentz and Poincare

Covered by
[Proper orthochronous Lorentz transformations and Poincaré coordinates](../roadmap/spacetime/lorentz-and-poincare.md),
lines 208 to 215.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.ProperLorentz` | abbrev | 209 | Proper, time-orientation-preserving linear transformations of Minkowski space. |
| `YangMills.PoincareCoordinates` | abbrev | 215 | Standard coordinates on the full proper orthochronous Poincaré group. |

### Poincare action

Covered by [Poincaré action](../roadmap/wightman/poincare-action.md), lines
217 to 250.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.PoincareAction` | structure | 219 | An action in any homeomorphic coordinate system, with its group law and pullback of tests fixed by the ordinary affine action on spacetime. |
| `YangMills.PoincareAction.Symmetry` | field | 220 | none |
| `YangMills.PoincareAction.one` | field | 221 | none |
| `YangMills.PoincareAction.mul` | field | 222 | none |
| `YangMills.PoincareAction.topology` | field | 223 | none |
| `YangMills.PoincareAction.onStates` | field | 224 | none |
| `YangMills.PoincareAction.onLabels` | field | 225 | none |
| `YangMills.PoincareAction.onTests` | field | 226 | none |
| `YangMills.PoincareAction.pureTranslation` | field | 227 | none |
| `YangMills.PoincareAction.identity` | field | 228 | none |
| `YangMills.PoincareAction.composition` | field | 229 | none |
| `YangMills.PoincareAction.unitary` | field | 231 | none |
| `YangMills.PoincareAction.stronglyContinuous` | field | 233 | none |
| `YangMills.PoincareAction.coordinates` | field | 235 | none |
| `YangMills.PoincareAction.identityCoordinates` | field | 236 | none |
| `YangMills.PoincareAction.productCoordinates` | field | 237 | none |
| `YangMills.PoincareAction.translationCoordinates` | field | 240 | none |
| `YangMills.PoincareAction.pullback` | field | 242 | none |
| `YangMills.PoincareAction.translationZero` | field | 244 | none |
| `YangMills.PoincareAction.translationAdd` | field | 245 | none |

Lines 248 to 250 register the fields `one`, `mul` and `topology` (the unit,
the product and the topology of the symmetry type) as instances. As in the
translation representation, the field named `unitary` (line 231) asserts only
that each operator preserves norms.

## Wightman axioms W0–W3

The file marks this section with a header at line 252.

### Wightman theory

Covered by [Wightman theory data](../roadmap/wightman/wightman-theory.md),
lines 254 to 262.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WightmanTheory` | structure | 255 | The observable data of a relativistic quantum field theory. |
| `YangMills.WightmanTheory.fields` | field | 256 | none |
| `YangMills.WightmanTheory.adjointLabel` | field | 257 | none |
| `YangMills.WightmanTheory.translations` | field | 258 | none |
| `YangMills.WightmanTheory.energyMomentum` | field | 259 | none |
| `YangMills.WightmanTheory.poincare` | field | 260 | none |
| `YangMills.WightmanTheory.translationCompatibility` | field | 261 | none |

The structures from line 270 to line 319 sit in the namespace `WightmanTheory`
(lines 264 to 321), where line 266 declares the Hilbert space and the label
space as section variables.

### Axiom W0

Covered by [Axiom W0: spectrum condition and unique vacuum](../roadmap/wightman/axiom-w0.md),
lines 266 and 268 to 278.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WightmanTheory.W0` | structure | 270 | W0: Hilbert-space covariance, the spectrum condition, and uniqueness of the invariant vacuum. |
| `YangMills.WightmanTheory.W0.spectralRepresentation` | field | 271 | none |
| `YangMills.WightmanTheory.W0.positiveEnergy` | field | 274 | none |
| `YangMills.WightmanTheory.W0.uniqueVacuum` | field | 276 | none |

The variable named `momentum` in `spectralRepresentation` (line 271) is the
argument of both the characteristic function and the translation operator, so
it plays the part of a translation vector. The docstring names Hilbert-space
covariance, for which `W0` has no field: the translation representation and
the Poincaré action in the theory's data carry it.

### Axiom W1

Covered by [Axiom W1: fields on a common dense domain](../roadmap/wightman/axiom-w1.md),
lines 266 and 280 to 284.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WightmanTheory.W1` | structure | 282 | W1: fields are tempered operator-valued distributions on a common dense invariant domain, with the vacuum cyclic. |
| `YangMills.WightmanTheory.W1.domain` | field | 283 | none |
| `YangMills.WightmanTheory.W1.adjoint` | field | 284 | none |

### Axiom W2

Covered by [Axiom W2: Poincaré covariance](../roadmap/wightman/axiom-w2.md),
lines 266 and 286 to 307.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WightmanTheory.W2` | structure | 287 | W2: Poincaré covariance of the fields and their common domain. |
| `YangMills.WightmanTheory.W2.labelIdentity` | field | 288 | none |
| `YangMills.WightmanTheory.W2.labelComposition` | field | 290 | none |
| `YangMills.WightmanTheory.W2.domainInvariant` | field | 294 | none |
| `YangMills.WightmanTheory.W2.vacuumInvariant` | field | 297 | none |
| `YangMills.WightmanTheory.W2.fieldCovariance` | field | 300 | none |

### Axiom W3

Covered by [Axiom W3: locality](../roadmap/wightman/axiom-w3.md), lines 266
and 309 to 311.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WightmanTheory.W3` | structure | 310 | W3: local commutativity at spacelike separation. |
| `YangMills.WightmanTheory.W3.locality` | field | 311 | none |

### Wightman axioms

Covered by [The Wightman axioms](../roadmap/wightman/wightman-axioms.md),
lines 266 and 313 to 319.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.WightmanTheory.Axioms` | structure | 315 | The four Wightman axioms are separate fields so the Comparator checks each one explicitly. |
| `YangMills.WightmanTheory.Axioms.w0` | field | 316 | none |
| `YangMills.WightmanTheory.Axioms.w1` | field | 317 | none |
| `YangMills.WightmanTheory.Axioms.w2` | field | 318 | none |
| `YangMills.WightmanTheory.Axioms.w3` | field | 319 | none |

The docstring refers to the Comparator, the checker that upstream's README
names in its verification section (README lines 42 and 48).
