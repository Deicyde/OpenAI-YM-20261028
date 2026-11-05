import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Bills

/-!
# Put powers (including the 2D+2 envelope) inside the budget

`‖x‖` on the read space is the pi sup norm; we price also the Euclidean
counting norm. Raw power use `power_on_raw`: additional *real* b and g costs
required. No small-g assumption. None of these estimates erase even one
color coordinate; the exponential reservoir that paid the joint norm bill
is still earned on all I coordinates.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C
open Function Filter Set Matrix MeasureTheory WithLp
open Next.SectorChange.Gaussian
open AnalyticBridge.LocalGaussianLaws
open scoped Topology BigOperators InnerProductSpace

variable {I : Type} [Fintype I]
variable {K : ℕ} {E M : ℝ}

/-- Helper to expose explicit norm powers in the budget. -/
def powerBill (K : ℕ) (E : ℝ) (h : ℕ) :=
  let r := reserve K E / ((h:ℝ)+1)
  (2*(1+r⁻¹))^h











/-- Allow explicit raw scaling. Taking b,g independent of x is NOT
required, so this is not necessarily a uniformly bounded raw bill. -/
def growth (K : ℕ) (E : ℝ) (b : Vec I) (g : ℝ) (h : ℕ) :=
  (1+countingNorm b+|g|)^h * powerBill K E h



section
variable {μ : Measure (Vec I)}

def MomentOfNorms (μ : Measure (Vec I)) (K : ℕ) (E : ℝ) (h : ℕ) :=
    Costed K E (powerBill K E h) μ (id : Vec I→Vec I) (fun z => (1+‖z‖)^h) ∧
    Costed K E (powerBill K E h) μ (id : Vec I→Vec I) (fun z => (1+countingNorm z)^h)



/-- No real norm bars needed in first-power use of this positive estimate. -/
lemma MomentOfNorms.use {h : ℕ} (hc : MomentOfNorms μ K E h) :
    ((∫ z, (1+‖z‖)^h ∂μ) ≤ powerBill K E h * kiln K E) ∧
    ((∫ z, (1+countingNorm z)^h ∂μ) ≤ powerBill K E h * kiln K E) := by
  have he : ∀ z : Vec I, 0 ≤ (1+countingNorm z)^h := fun z => by have := countingNorm_nonneg z; positivity
  have hy : ∀ z : Vec I, 0 ≤ (1+‖z‖)^h := fun z => by positivity
  simpa only [Real.norm_of_nonneg (he _), Real.norm_of_nonneg (hy _)] using
    And.intro hc.1.first_bound hc.2.first_bound

end
end YM.PhysicalNext.WeightedGaussianMarginal45C
