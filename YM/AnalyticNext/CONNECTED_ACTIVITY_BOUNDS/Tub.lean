import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Dice
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Kettle

/-!
# Quick analytic row and ratio (Haar) vertices

Haar relative uses ONE paid scale. Extension via ψ; on support of γ
it's the actual J. Paired normalization letter j=0 standard region
(hole comparisons earned before leasing). Foot price independent of
period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Jewels
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

abbrev Flick (S : StepData c f) := Rack S ⊕ Bond f ⊕ Bond f -- shell, paired, regularRatio

def pivot (S : StepData c f) : Flick S → Site c := Sum.elim (crib S) (Sum.elim (home S) (home S))
def column (S : StepData c f) (x : ℝ) (i : Flick S) := den (pivot S i) 640 (radiusB x)

def hat (x : ℝ) (D : Patch) (q : Chi) (N : ChartRatio G) (a : G.Color) :=
    ψ x D q a*(N.J a-1)

def slash (Y : Mint T F A x) (β : ℝ) (N : ChartRatio G) (a : ArrayR G f) : Flick S → ℝ
  | .inl i => if crib S i ∈ A.dome (200*radiusB x) then 0 else
      -- protect all U stencils. exact on masks; even after dropping is
      -- real (unmarked). Keep V tails and M cohorts on formal data.
      Real.exp (-β * robe Y (pulls S (2*radiusB x) (crib S i)) a * pureBooth Y a i) - 1
  | .inr (.inl i) => if i∈padB A (200*radiusB x) then 0 else Real.exp (paired Y i)-1
  | .inr (.inr i) => if i∈activeB A F (radiusB x) ∧ i∉padB A (304*radiusB x) then hat x S.patch Y.q N (lie a i) else 0

lemma scale_down (G : Gauge) (D : Patch) (p : ℕ) {e : ℝ} (he : e<1/2) : ∀ᶠ x : ℝ in atTop,
    allowance G D x 1 p ≤ amend G D x e := by
  filter_upwards [stipend G D 0 p 1 zero_le_one he,pos_size G D] with x hx ht
  rw [one_mul,pow_zero,mul_one] at hx; unfold allowance; rw [pow_one]
  exact (mul_le_mul_of_nonneg_right (bump G D x p) ht.1.le).trans hx










end YM.AnalyticNext.ConnectedActivity.Jewels
