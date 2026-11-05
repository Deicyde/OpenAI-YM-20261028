import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tub
import YM.Push.RELAY_DIFFERENCE.Applications
import YM.Push.RELAY_DIFFERENCE.TwoSided

/-!
# The bought coefficients applied in authentic threshold range

One-call purchases. Width tests including E projected at output stage.
Pre-L support reserve a (application pays marked variants through a
finite list). Proof maintains hats H_f from same H_c. Only consumes
the labelled estimates at *input*; prices pay whole output orientation
expansion without relabelling. No differential assumptions on output
E or K. Explicitly distinguish this from claiming that `Valid` suffices
for a general discrete RG producer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Cab
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Paths  
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

lemma amend_b (G : Gauge) (D : Patch) (C : ℝ) (hC : 0≤C) (ρ : Tempo) : ∀ᶠ x : ℝ in atTop,
    ∀ (β Λ : ℝ), OnBand G D x β → Λ ≤ betaF G x D.L^(1/8:ℝ) →
    let t := fiery G x D.L; let u := amend G D x ρ.rate; let z := β*Aff.weight
    |Aff.weight| * t^2 * Λ ≤ u ∧ |z| * t^3*C ≤ u ∧ |z| * t^4*C ≤ u := by
  have hp := Aff.weight_pos
  filter_upwards [burn_card G D (4*Aff.weight*C) (by positivity) 0 ρ.open_,Delay.shift_pos G D.L,
    instills G D Aff.weight ρ.rate (5/8) 0 hp.le (by linarith [ρ.open_]),pos_size G D, scale_down G D 0 (show (3/8:ℝ) < 1/2 by norm_num),
    (slow G D).eventually (ge_mem_nhds zero_lt_one)] with x hx he hv hh hy hr β Λ hb hl t u z
  have ht : 0<t := hh.1
  have h1 : t≤1 := by simpa [t,allowance,pieces] using hr
  have hβ : 0≤ β := (by linarith only [he,hb.1]); let b := betaF G x D.L
  have hh : |z| * t^3*C ≤ u := by
    rw [abs_of_nonneg (show 0≤z from mul_nonneg hβ hp.le)]
    calc
      _ ≤ ((4*b)*Aff.weight)*t^3*C := by unfold z; gcongr; exact hb.2
      _ = 4*Aff.weight*C*b*allowance G D x 3 0 := by unfold t allowance pieces; ring
      _ ≤ _ := hx
  rw [abs_of_nonneg hp.le]
  refine ⟨?_,hh,?_⟩
  · rw [pow_zero,mul_one] at hv; apply le_trans _ hv
    let X := amend G D x (3/8)
    have hu : t≤ X := by simpa [t,allowance,pieces,X] using hy
    calc
      _ ≤ Aff.weight*t^2*b^(1/8:ℝ) := by gcongr
      _ ≤ Aff.weight*X^2*b^(1/8:ℝ) := by gcongr
      _ = _ := by
        rw [mul_assoc]; unfold X amend b
        rw [pow_two,← Real.rpow_add he,← Real.rpow_add he]; ring_nf
  apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht.le h1 (show 3≤4 by omega)) (abs_nonneg z)) hC) hh




end YM.AnalyticNext.ConnectedActivity.Cab
