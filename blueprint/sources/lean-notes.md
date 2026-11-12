# Lean-side notes

Observations about how the four Lean files of the closure state their
definitions, kept here because the articles state only the mathematics. Every
Mathlib reference below was checked against the pinned Mathlib checkout,
commit 81a5d257c8e410db227a6665ed08f64fea08e997; paths are relative to its
root, and line numbers are those of that commit.

## Mathlib notions

- **Schwartz functions.** `SchwartzMap E F` (Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean,
  line 78) is the space of smooth functions $f : E \to F$ such that
  $\|x\|^k \, \|D^n f(x)\|$ is bounded in $x$ for all $k, n$. The project's
  `TestFunction` is `SchwartzMap Spacetime ℂ`. `SchwartzMap.postcompCLM` (same
  file, line 1033) composes with a continuous linear map; `conjugateTest`
  applies it to complex conjugation taken as a real-linear map, so it is
  real-linear.
- **Compactly supported test functions.** `TestFunction Ω F n`
  (Mathlib/Analysis/Distribution/TestFunction.lean, line 67) is the space of
  $n$ times continuously differentiable functions with compact support whose
  topological support lies in the open set $\Omega$; with $n = \top$ they are
  smooth. `SeparatedTest n` is `TestFunction (separated n) ℂ ⊤`.
- **Topological support.** `tsupport f` is the closure of the set where $f$ is
  nonzero (Mathlib/Topology/Algebra/Support.lean, line 50, the additive form of
  `mulTSupport`).
- **Characteristic function.** `charFun μ t` is
  $\int e^{i\langle x, t\rangle}\, d\mu(x)$
  (Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean, line 126),
  for the real inner product of the space. On `Spacetime` that product is the
  Euclidean one, $\sum_i x_i t_i$ (`PiLp.inner_apply`,
  Mathlib/Analysis/InnerProductSpace/PiL2.lean, line 103, and
  `RCLike.inner_apply`, Mathlib/Analysis/InnerProductSpace/Basic.lean,
  line 914), not a Minkowski product.
- **Inner products.** Mathlib's inner product is conjugate-linear in its first
  argument and linear in its second: $\langle r x, y\rangle = \bar r \langle x,
  y\rangle$ (`inner_smul_left`, Mathlib/Analysis/InnerProductSpace/Basic.lean,
  line 105) and $\langle x, r y\rangle = r \langle x, y\rangle$
  (`inner_smul_right`, line 115).
- **Adjoint.** `ContinuousLinearMap.adjoint`
  (Mathlib/Analysis/InnerProductSpace/Adjoint.lean, line 114) is the adjoint
  $A^\dagger$ of a bounded operator, with
  $\langle A^\dagger y, x\rangle = \langle y, A x\rangle$
  (`adjoint_inner_left`, line 123).
- **Unitary matrices.** `Matrix.unitaryGroup n α`
  (Mathlib/LinearAlgebra/UnitaryGroup.lean, line 60) is `unitary (Matrix n n α)`,
  the matrices $U$ with $U^* U = 1$ and $U U^* = 1$
  (Mathlib/Algebra/Star/Unitary.lean, line 35), where the star of a matrix is
  its conjugate transpose (`Matrix.star_eq_conjTranspose`,
  Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean, line 413).
- **Exponential.** `NormedSpace.exp`
  (Mathlib/Analysis/Normed/Algebra/Exponential.lean, line 127) sums the series
  $\sum_k x^k / k!$; its junk value 1 applies only in an algebra with no
  structure of algebra over the rationals. For complex matrices it is the
  matrix exponential, as its docstring says.
- **Frobenius scope.** `Matrix.Norms.Frobenius`
  (Mathlib/Analysis/Matrix/Normed.lean, line 670) turns on the Frobenius norm
  instances on matrices. Their norm is built with
  `PiLp.seminormedAddCommGroupToPi` (Mathlib/Analysis/Normed/Lp/PiLp.lean,
  line 1246), which keeps the product uniformity by construction, so opening
  the scope changes no topology on matrices. No statement in the four files
  writes the norm of a matrix.
- **Haar measure.** `IsHaarMeasure μ` (Mathlib/MeasureTheory/Group/Measure.lean,
  line 775) asks $\mu$ to be finite on compact sets, left-invariant (the image
  of $\mu$ under $h \mapsto g h$ is $\mu$ for every $g$, `IsMulLeftInvariant`,
  Mathlib/MeasureTheory/Group/Defs.lean, line 77) and positive on nonempty
  open sets.
- **Measures positive on open sets.** `IsOpenPosMeasure μ`
  (Mathlib/MeasureTheory/Measure/OpenPos.lean, line 39): $\mu(U) \ne 0$ for
  every nonempty open set $U$.
- **Probability and finite measures.** `IsProbabilityMeasure μ`: the whole
  space has measure 1 (Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean,
  line 64). `IsFiniteMeasure μ`: the whole space has finite measure
  (Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean, line 35).
- **Real-valued measure.** `μ.real s` is $\mu(s)$ as a real number
  (Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean, line 101); a set of
  infinite measure gets 0. The diagonal measures of an energy–momentum measure
  are finite, so this value does not arise there.
- **Product measure and density.** `Measure.pi`
  (Mathlib/MeasureTheory/Constructions/Pi.lean, line 210) is the finite product
  measure, which gives each box the product of the factors' measures when the
  factors are σ-finite (`pi_pi`, line 290). `μ.withDensity f`
  (Mathlib/MeasureTheory/Measure/WithDensity.lean, line 39) gives each
  measurable set $s$ the mass $\int_s f \, d\mu$, a lower Lebesgue integral.
- **Centered representatives.** `ZMod.valMinAbs`
  (Mathlib/Data/ZMod/ValMinAbs.lean, line 23) sends a residue modulo
  $n \ge 1$ to its representative in $(-n/2, n/2]$ (`valMinAbs_mem_Ioc`,
  line 71).
- **Lp types.** `WithLp p V` (Mathlib/Analysis/Normed/Lp/WithLp.lean, line 50)
  is a copy of `V`, entered and left through `toLp` and `ofLp`;
  `PiLp p α` is `WithLp p (∀ i, α i)` (Mathlib/Analysis/Normed/Lp/PiLp.lean,
  line 85), whose norm for $p = 2$ is $\sqrt{\sum_i \|x_i\|^2}$
  (`PiLp.norm_eq_of_L2`, line 776); and `EuclideanSpace 𝕜 n` is
  `PiLp 2 (fun _ : n => 𝕜)` (Mathlib/Analysis/InnerProductSpace/PiL2.lean,
  line 113). So `Spacetime`, `Space`, `Points n`, `OPEPoint` and `OPEPoints n`
  carry Euclidean norms. `OPEComplexTimes n` and `OPESpacePoints n` are plain
  function types, which Mathlib gives the supremum norm (finite products,
  Mathlib/Analysis/Normed/Group/Constructions.lean, line 300).
- **Volume.** On a finite-dimensional real inner product space with its Borel
  σ-algebra, `volume` is `measureSpaceOfInnerProductSpace`
  (Mathlib/MeasureTheory/Measure/Haar/OfBasis.lean, line 309), the additive
  Haar measure normalized by an orthonormal basis. On `EuclideanSpace ℝ ι` it
  corresponds to Lebesgue measure on `ι → ℝ`
  (`EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`,
  Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean, line 124).
  Mathlib declares no other measure-space instance on `WithLp` or `PiLp`.
- **Unconditional sums.** `HasSum f a` (Mathlib/Topology/Algebra/InfiniteSum/Defs.lean,
  line 106, the additive form of `HasProd`) says that the sums of $f$ over
  finite sets converge to $a$ as the finite sets grow (the unconditional
  summation filter, Mathlib/Topology/Algebra/InfiniteSum/SummationFilter.lean,
  line 168), so the sum does not depend on the order of the terms.
- **Smoothness exponents.** Under the scope `ContDiff`, `∞` is smoothness and
  `ω` analyticity (Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean,
  lines 116 to 120); `ContDiffOn` is defined in
  Mathlib/Analysis/Calculus/ContDiff/Defs.lean, line 472.
- **Topology on units.** The units of a topological monoid carry the topology
  induced by $u \mapsto (u, u^{-1})$ (Mathlib/Topology/Algebra/Constructions.lean,
  line 101). `ProperLorentz` has the subspace topology of the units of the
  continuous linear maps of `Spacetime`, and `PoincareCoordinates` the product
  topology with `Spacetime`.
- **Enumerations.** `Fintype.equivFin α` (Mathlib/Data/Fintype/EquivFin.lean,
  line 80) is a noncomputable bijection from `α` onto `Fin (card α)`, fixed by
  choice.
- **Filters.** `atTop` (Mathlib/Order/Filter/AtTopBot/Defs.lean, line 39):
  `∀ᶠ k in atTop, P k` means that $P(k)$ holds for all large $k$. `𝓝[>] 0` is
  `nhdsWithin 0 (Set.Ioi 0)` (Mathlib/Topology/Defs/Filter.lean, line 155):
  `∀ᶠ r in 𝓝[>] 0, P r` means that $P(r)$ holds for all $r$ in some interval
  $(0, \delta)$ with $\delta > 0$ (`mem_nhdsGT_iff_exists_Ioo_subset`,
  Mathlib/Topology/Order/LeftRightNhds.lean, line 102). `f =ᶠ[l] g`
  (`Filter.EventuallyEq`, Mathlib/Order/Filter/Defs.lean, line 297) means
  `∀ᶠ x in l, f x = g x`; along `𝓝[>] 0` it says that $f$ and $g$ agree on
  some interval $(0, \delta)$ with $\delta > 0$.

## Junk-value conventions

Mathlib extends some partial operations to total ones, and the statements read
them literally:

- A Bochner integral of a function that is not integrable is 0
  (`MeasureTheory.integral_undef`, Mathlib/MeasureTheory/Integral/Bochner/Basic.lean,
  line 202). This convention enters the normalizing integral of the Wilson
  measure, the finite moments, the limit in the ordered continuum limit, the
  mixture and boundary conditions of the reconstruction, and the integrals in
  the Wick profiles.
- Division by zero gives 0 (`div_zero`, Mathlib/Algebra/GroupWithZero/Basic.lean,
  line 407). It enters the density of the Wilson measure when the normalizing
  integral is 0; the factor $1/(2E)$ of a mode's kernel where $E = 0$, that is
  at zero momentum for a mode of mass 0; and the ratio in the running condition
  when the denominator of the lattice spacing is 1, where the logarithm is
  $\log 1 = 0$ (`Real.log_one`, Mathlib/Analysis/SpecialFunctions/Log/Basic.lean,
  line 106). The running condition is asked only for all large $N$, and the
  strictly increasing denominators can equal 1 only at $N = 0$, so the last
  case does not affect it.
- `ENNReal.ofReal` sends negative numbers to 0 (Mathlib/Data/ENNReal/Basic.lean,
  line 230; `ENNReal.ofReal_of_nonpos`, Mathlib/Data/ENNReal/Real.lean,
  line 196). The Wilson measure applies it to a positive number divided by a
  nonnegative integral, which is never negative, so the convention has no
  effect there.

## Naming observations

Names in the Lean that could mislead a reader, and that the articles therefore
do not echo:

- The project's `TestFunction` is the Schwartz space; Mathlib's `TestFunction`
  is a space of compactly supported smooth functions, used by `SeparatedTest`.
- The fields named `unitary`, in `TranslationAction` and `PoincareAction`,
  assert only that each operator preserves norms.
- The variable named `momentum` in the field `spectralRepresentation` of `W0`
  is a translation vector, the argument of the translation operator.
- The abbreviations with the prefix `OPE` (`OPEPoint`, `OPEPoints`,
  `OPEComplexTimes` and `OPESpacePoints`) are used only by the helpers of the
  analytic continuation (`orderedTube`, `complexShift`, `imaginaryTimes`,
  `spatialPoints` and `tensorTest`) and by the reconstruction conditions. The
  operator product expansion itself writes `Spacetime`, although the docstring
  of `OPEPoint` calls it the spacetime used by the OPE estimates. `OPEPoint`
  and `OPEPoints` restate the types `Spacetime` and `Points`.
- Namespaces do not record dependencies: `SpacelikeSeparated` sits in
  `FieldSystem`, `separated` and `SeparatedTest` in `WilsonFamily`, and
  `Within`, `Clear`, `timePair`, `Mode`, `Track`, `wickProfile`,
  `orderedTube`, `complexShift`, `imaginaryTimes`, `spatialPoints`,
  `tensorTest` and the `OPE` abbreviations in `Hierarchy`, yet none of them
  uses an object of its namespace's type.
- `wilsonEnergy` is the Wilson action and `wilsonLaw` the Wilson measure.

## Build options

The repository's lakefile.toml sets `maxHeartbeats = 0`, which removes the
heartbeat limit, and `maxRecDepth = 4096` for the whole package, as upstream's
lakefile does. No
`set_option` other than `autoImplicit` appears in the four files.
