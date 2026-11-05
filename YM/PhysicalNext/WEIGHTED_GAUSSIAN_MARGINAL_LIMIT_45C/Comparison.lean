import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Bills

/-!
# Quantitative comparison in the committed prices

The old log inequality is used *pointwise*. We pay the norm of the
likelihood **difference** times a test satisfying `Moderate`, by two
integrable functions: the earned exponential moment envelope under each of
the two actual laws, with the same prices at K. This way no quadratic-exponential
likelihood powers have to be purchased, no higher p-th density threshold is
assumed, and we do not pretend the pointwise log bound is a uniform relative
bound. Rate accounts for the energy term and one local
cardinality bound.
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

/-- Currency to turn the affine log bound into integrated cost against
both Gaussians. -/
def logBill (K : ℕ) (E : ℝ) : ℝ := 2*(K:ℝ) + 2*(reserve K E)⁻¹

/-- Per unit `Moderate` bound. (See Polynomial for the price per
coefficient norm.) -/
def errorUnit (K : ℕ) (E x : ℝ) : ℝ := logBill K E * (2*kiln K E) * speed x







variable {I : Type} [Fintype I] [DecidableEq I]
variable {K : ℕ} {E M x : ℝ} {C B : Gaussian.Table I} {δ : Vec I}



variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] {f : Vec I → X}

/-- Supplies integrability, moments & tail certificates, and the exact
likelihood-integral identity on the way to the estimate (even as an L¹
bound of the reweighted difference). Use in particular on complex tests.
The shifted argument `-δ` of `replace` always means this polarity. -/
structure Estimate (K : ℕ) (E M x : ℝ) (C B : Gaussian.Table I) (δ : Vec I)
    (f : Vec I → X) : Prop where
  source : Costed K E M (shift C δ) (id : Vec I → Vec I) f
  reference : Costed K E M (cloud B) (id : Vec I → Vec I) f
  reweighted : Integrable (fun z => Density.replace C B (-δ) z • f z) (cloud B)
  exact_id : (∫ z,f z ∂shift C δ) = ∫ z, Density.replace C B (-δ) z • f z ∂cloud B
  weighted_error : (∫ z, ‖Density.replace C B (-δ) z • f z - f z‖ ∂cloud B) ≤ M*errorUnit K E x
  compare : ‖(∫ z, f z ∂shift C δ) - (∫ z,f z ∂cloud B)‖ ≤ M*errorUnit K E x

section
variable [OpensMeasurableSpace X] [SecondCountableTopology X]


end

omit [MeasurableSpace X] in
lemma shifted_into_section (C : Gaussian.Table I) (δ : Vec I) (f : Vec I → X) :
    (∫ z, f z ∂shift C δ) = (∫ z, f (δ+z) ∂cloud C) := (PhysicalGaussianSwitch.shift_int ..).2



end YM.PhysicalNext.WeightedGaussianMarginal45C
