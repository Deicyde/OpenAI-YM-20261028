import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Polynomial
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Powers
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Marginal


/-!
# Actual reads, not just marginals

Result-facing package to apply to the actual step. Spells also the full
cloud integrands with their original g on the physical side. In the
normalized use only compare with a **common** centering; all pullbacks and
complete record kept exact. Includes also unscaled income (nonuniform
prices!). Any tail reading in this API uses the normalized location Y (on
the full cloud in `FromRead`, already centered on the reference in BOTH
cases, even for estimates with a raw polynomial). Raw-tail threshold
accordingly must still include b and g.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C
open Function Filter Set Matrix MeasureTheory
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian
open AnalyticBridge.LocalGaussianLaws
open SectorTools
open SectorTools.PhysicalGaussianSwitch (shift)
open scoped Topology BigOperators

variable {I L N : Type} [Fintype I] [Fintype L] [Fintype N]
variable [DecidableEq I] [DecidableEq L] [DecidableEq N]
variable {E M x : ℝ} {K d : ℕ} {Q : Gaussian.Table N} {J : Gaussian.Table L}
variable {a : Vec N} {b : Vec L} {e : I ↪ N} {l : I ↪ L} {g : ℝ}

/-- On the input side, including polarity. The law induced on the same
centered scaled read `normalizeRead (b ∘ l) g x` from actual physical x is
`shift C δ` with `δ = g⁻¹ • (a ∘ e - b ∘ l)`. -/
structure Reading (K : ℕ) (E x : ℝ) (Q : Gaussian.Table N) (J : Gaussian.Table L) (a : Vec N) (b : Vec L)
    (g : ℝ) (e : I ↪ N) (l : I ↪ L) : Prop where
  pos : Q.PosDef
  pos_free : J.PosDef
  scale : 0 < g
  earned : Prices K E x (Q.submatrix e e) (J.submatrix l l) (changeMean (a ∘ e) (b ∘ l) g)



section read
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
variable {p : Vec I → X}

/-- The common-coordinate test `p` and the corresponding full-cloud
tests. Construct applications with the latter specified literally. -/
structure FromRead (K : ℕ) (E M x : ℝ) (Q : Gaussian.Table N) (J : Gaussian.Table L) (a : Vec N) (b : Vec L)
    (g : ℝ) (e : I ↪ N) (l : I ↪ L) (p : Vec I → X) (pt : Vec N → X) (pr : Vec L → X) : Prop where
  estimate : Estimate K E M x (Q.submatrix e e) (J.submatrix l l) (changeMean (a ∘ e) (b ∘ l) g) p
  actual : Costed K E M (cloud Q) (normalizeRead (b ∘ l) g ∘ physicalRead a g e) pt
  actual_reference : Costed K E M (cloud J) (normalizeRead (b ∘ l) g ∘ physicalRead b g l) pr
  actual_eq : (∫ z, pt z ∂cloud Q) = ∫ z, p z ∂shift (Q.submatrix e e) (changeMean (a ∘ e) (b ∘ l) g)
  actual_eq_reference : (∫ z, pr z ∂cloud J) = ∫ z, p z ∂cloud (J.submatrix l l)
  actual_compare : ‖(∫ z, pt z ∂cloud Q)-(∫ z,pr z ∂cloud J)‖ ≤ M*errorUnit K E x

/-- Use from centered/scaled reads. Costs the original full polynomials
of those fluctuation units under the two actual cloud integrations. -/
abbrev OnNormalized (K : ℕ) (E M x : ℝ) (Q : Gaussian.Table N) (J : Gaussian.Table L) (a : Vec N) (b : Vec L)
    (g : ℝ) (e : I ↪ N) (l : I ↪ L) (f : Vec I → X) :=
  FromRead K E M x Q J a b g e l f (f ∘ normalizeRead (b ∘ l) g ∘ physicalRead a g e)
    (f ∘ normalizeRead (b ∘ l) g ∘ physicalRead b g l)

/-- Use instead for an unscaled `f`; callers retain raw M. Still
includes the estimate, exact reweighting and tail certificates on the way.
E.g. reads `f` at `(b+g • z) ∘ l`, using Z IN `cloud J`. -/
abbrev OnRaw (K : ℕ) (E M x : ℝ) (Q : Gaussian.Table N) (J : Gaussian.Table L) (a : Vec N) (b : Vec L)
    (g : ℝ) (e : I ↪ N) (l : I ↪ L) (f : Vec I → X) :=
  FromRead K E M x Q J a b g e l (f ∘ restoreRead (b ∘ l) g) (f ∘ physicalRead a g e) (f ∘ physicalRead b g l)

variable [OpensMeasurableSpace X] [SecondCountableTopology X]




end read

/-- Result-facing per-degree estimates on the two committed clouds.
`OnNormalized` / `OnRaw`: both the same-marginal Estimate and the
costs & comparison on the full registers. Core prices kept, so can apply
also to e.g. several such tests simultaneously (subject to the polynomials'
actual norms and degrees). -/
structure Readout (K d : ℕ) (E x : ℝ) (Q : Gaussian.Table N) (J : Gaussian.Table L) (a : Vec N) (b : Vec L)
    (g : ℝ) (e : I ↪ N) (l : I ↪ L) : Prop where
  costs : Reading K E x Q J a b g e l
  moments :
    let p := 2*d+2; let M := powerBill K E p
    OnNormalized K E M x Q J a b g e l (fun z : Vec I => (1+‖z‖)^p) ∧
    OnNormalized K E M x Q J a b g e l (fun z : Vec I => (1+countingNorm z)^p)
  normal (P : MvPolynomial I ℂ) (hp : P.totalDegree ≤ d) :
    OnNormalized K E (coefficientNorm P * normalBill K E d) x Q J a b g e l (peval P)
  /-- Every combination of powers, e.g. on local Lie/color coordinates. -/
  mixed (s : I →₀ ℕ) (hs : s.sum (fun _ j => j) ≤ d) :
    OnNormalized K E (normalBill K E d) x Q J a b g e l (absMixed s)
  raw_moments :
    let p := 2*d+2; let M := growth K E (b ∘ l) g p
    OnRaw K E M x Q J a b g e l (fun z : Vec I => (1+‖z‖)^p) ∧
    OnRaw K E M x Q J a b g e l (fun z : Vec I => (1+countingNorm z)^p)
  raw_result (P : MvPolynomial I ℂ) (hp : P.totalDegree ≤ d) :
    OnRaw K E (coefficientNorm P * polyBill K E d ‖b ∘ l‖ g) x Q J a b g e l (peval P)
  raw_mixed (s : I →₀ ℕ) (hs : s.sum (fun _ j => j) ≤ d) :
    OnRaw K E (polyBill K E d ‖b ∘ l‖ g) x Q J a b g e l (absMixed s)







end YM.PhysicalNext.WeightedGaussianMarginal45C
