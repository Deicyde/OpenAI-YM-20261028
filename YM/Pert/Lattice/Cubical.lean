import YM.Pert.Lattice.Geometry
import YM.Space.Configurations
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
/-! Massless Wilson top covariance multiplier on the infinite cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Full
open Lattice Filter MeasureTheory Metric Set
open scoped Topology BigOperators

lemma norm_four (x : E4) : ‖x‖^2 = ∑ i : Axis, (x i)^2 := by rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]; simp
def cube : Set E4 := {p | ∀ i, |p i| ≤ Real.pi}
lemma cube_subset : cube ⊆ ball 0 (4*Real.pi) := by
  intro x hx; rw [mem_ball,dist_zero_right]
  have he := norm_four x
  have hsum := Finset.sum_le_sum (fun (i : Axis) (_ : i∈Finset.univ) => show x i ^ 2 ≤ Real.pi ^ 2 by grw [←sq_abs, (hx : ∀ i, _ ≤ _) i])
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsum
  have := Real.pi_pos; norm_num [nsmul_eq_mul] at hsum; nlinarith
lemma cube_compact : IsCompact cube := by
  refine (isCompact_closedBall (0:E4) (4*Real.pi)).of_isClosed_subset (by convert! (isClosed_iInter (fun i : Axis => isClosed_le (by fun_prop : Continuous (fun x : E4 => |x i|)) (g:=(fun _ => Real.pi)) continuous_const)); ext; simp [cube]) (cube_subset.trans ball_subset_closedBall)

def delta (p : E4) : ℝ := ∑ i : Axis, 4*(Real.sin (p i/2))^2
def volumeFactor : ℝ := (2*Real.pi)^(-4:ℤ)
def corner (z : Cover) (p : E4) : ℝ := ∑ i : Axis, (z i:ℝ)*p i
def wave (sine : Bool) (z : Cover) (p : E4) : ℝ := if sine then Real.sin (corner z p) else Real.cos (corner z p)
@[fun_prop] lemma delta_cont : Continuous delta := by unfold delta; fun_prop
@[fun_prop] lemma corner_cont (z : Cover) : Continuous (corner z) := by unfold corner; fun_prop
@[fun_prop] lemma wave_cont (s : Bool) (z : Cover) : Continuous (wave s z) := by unfold wave; split <;> fun_prop
lemma delta_bound {p : E4} (hp : p ∈ cube) : ‖p‖ ^ 2 ≤ delta p * ((Real.pi ^ 2)/4) := by
  have he := norm_four p
  rw [he,delta,Finset.sum_mul]; refine Finset.sum_le_sum (fun i hi => ?_)
  have ht := Real.mul_le_sin (x:=|p i|/2) (by positivity) (by gcongr; exact hp i)
  have hpi := Real.pi_pos
  have hle : |p i| ≤ Real.pi * Real.sin (|p i|/2) := by field_simp at ht; linarith
  suffices eq : (Real.sin (|p i|/2))^2=(Real.sin (p i/2))^2 by grw [← sq_abs (p i),hle, mul_pow,eq]; · ring_nf; exact le_rfl
  rcases le_total (p i) 0 with ha|ha; · rw [abs_of_nonpos ha,neg_div,Real.sin_neg]; ring_nf
  rw [abs_of_nonneg ha]
lemma delta_pos {p : E4} (hp : p ∈ cube) (hp0 : p≠0) : 0 < delta p := by
  have hb := delta_bound hp; have h := norm_pos_iff.mpr hp0
  have hv : 0 < Real.pi^2/4 := by positivity
  by_contra! ht; have := mul_nonpos_of_nonpos_of_nonneg ht hv.le; nlinarith
lemma delta_grade {p : E4} (hp : p∈cube) (hp0 : p≠0) : (delta p)⁻¹ ≤ (Real.pi^2/4)*‖p‖^(-(2:ℝ)) := by
  rw [Real.rpow_neg (by positivity), show (2:ℝ)=((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,← one_div (delta p), ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (delta_pos hp hp0) (sq_pos_of_pos (norm_pos_iff.mpr hp0))).2 (by rw [one_mul,mul_comm (Real.pi^2/4)]; exact delta_bound hp)
lemma delta_integrable : IntegrableOn (fun p : E4 => (delta p)⁻¹) cube := by
  let f := cube.indicator (fun p => (delta p)⁻¹)
  have hf : AEStronglyMeasurable f MeasureTheory.volume := (delta_cont.measurable.inv.indicator cube_compact.isClosed.measurableSet).aestronglyMeasurable
  have hp : ∀ᵐ p ∂volume.restrict (ball (0:E4) (4*Real.pi)), ‖f p‖ ≤ (Real.pi^2/4)*‖p‖^(-(2:ℝ)) := Filter.Eventually.of_forall (fun p => ?_)
  rotate_left
  · unfold f
    by_cases h : p∈cube; swap; · rw [indicator_of_notMem h]; simp only [norm_zero]; positivity
    by_cases hx : p=0
    · subst p; rw [indicator_of_mem h]; simp [cube,delta]; positivity
    rw [indicator_of_mem h, Real.norm_of_nonneg (inv_pos.mpr (delta_pos h hx)).le]; exact delta_grade h hx
  have hg := MeasureTheory.integrableOn_ball_of_norm_le_rpow (by simp : 1 ≤ Module.finrank ℝ E4) (by norm_num [E4,Axis] : (2:ℝ)<Module.finrank ℝ E4) hp hf
  apply (hg.mono_set cube_subset).congr_fun (fun x h => indicator_of_mem h _) cube_compact.isClosed.measurableSet
end YM.Pert.Full
