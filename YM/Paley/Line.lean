import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Support
import YM.Analysis.Nonnegative


/-!
# Paley Gaussian strip

Real `b` frequency: T(t) orbit +ib, shift imaginary positive ⇒ estimates
exp(b t), kill *negative*. Scalar version.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Paley
open Function Set Filter MeasureTheory Measure Complex  Topology
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators Real

def high := {z : ℂ | 0 ≤ z.im}
def loft := {z : ℂ | 0 < z.im}

lemma open_loft : IsOpen loft := isOpen_lt continuous_const continuous_im
lemma subset : loft ⊆ high := fun z h => le_of_lt (show 0<z.im from h)

def Z (s t : ℝ) := (t:ℂ)+(s:ℂ)*I
@[simp] lemma level (s t) : (Z s t).im=s := by simp [Z]
@[simp] lemma time (s t) : (Z s t).re=t := by simp [Z]
@[simp] lemma gap_zero (t) : Z 0 t=(t:ℂ) := by simp [Z]

structure Air (F : ℂ → ℂ) (C : ℝ) : Prop where
  connects : ContinuousOn F high
  straight : DifferentiableOn ℂ F loft
  bounded z (h : z ∈ high) : ‖F z‖ ≤ C

variable {F : ℂ → ℂ} {C : ℝ} (h : Air F C)
namespace Air
include h
lemma rate : 0 ≤ C := le_trans (norm_nonneg _) (h.bounded 0 (by simp [high]))
lemma cont (s : ℝ) (hs : 0 ≤ s) : Continuous (F ∘ Z s) := h.connects.comp_continuous
    (by unfold Z; fun_prop) (fun x => show 0 ≤ (Z _ _).im from by simpa using hs)
end Air

def probe (b ε : ℝ) (z : ℂ) := Complex.exp (-(b:ℂ)*z*I-(ε:ℂ)*z^2)
lemma probed (b ε s t : ℝ) : ‖probe b ε (Z s t)‖= Real.exp (-ε*t^2)*Real.exp (b*s+ε*s^2) := by
  rw [probe,Complex.norm_exp,← Real.exp_add]; congr 1
  simp [pow_two,mul_re,mul_im];ring
lemma monitors (b ε s : ℝ) : Continuous fun t => probe b ε (Z s t) := by unfold probe Z;fun_prop

include h
lemma finite (s b ε : ℝ) (hs : 0 ≤ s) (he : 0 < ε) : Integrable (fun t => F (Z s t)*probe b ε (Z s t)) := by
  let f (t : ℝ) := C * (Real.exp (-ε*t^2)*Real.exp (b*s+ε*s^2))
  have hf : Integrable f volume := ((integrable_exp_neg_mul_sq he).mul_const _).const_mul C
  apply hf.mono
    (((Air.cont h s hs).mul (monitors ..)).aestronglyMeasurable : AEStronglyMeasurable (fun t => F (Z s t)*probe b ε (Z s t)) volume)
  apply ae_of_all; intro t
  change ‖F (Z s t)*probe b ε (Z s t)‖ ≤ ‖f t‖; rw [norm_mul]; apply le_trans (mul_le_mul_of_nonneg_right
    (h.bounded _ (by simp [high,hs])) (norm_nonneg _))
  rw [probed]; exact Real.le_norm_self _

lemma wings (s b ε : ℝ) (hs : 0 ≤ s) (he : 0 < ε) :
    let v (t : ℝ) := ∫ i : ℝ in 0..s, F (Z i t)*probe b ε (Z i t)
    Tendsto v atTop (𝓝 0) ∧ Tendsto (fun t => v (-t)) atTop (𝓝 0) := by
  let U (t : ℝ) := C*(Real.exp (-ε*t^2) * Real.exp (|b| *s+ε*s^2))*s
  have hz : Tendsto U atTop (𝓝 0) := by
    have hp : Tendsto (fun t : ℝ => -ε*t^2) atTop atBot := (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr he)).mpr
      (tendsto_pow_atTop (by decide))
    simpa [U] using (((Real.tendsto_exp_atBot.comp hp).mul_const (Real.exp (|b| *s+ε*s^2))).const_mul C |>.mul_const s)
  intro v
  have ht (t : ℝ) : ‖v t‖ ≤ U t := by
    unfold v; unfold U
    have hz i (hi : i∈Set.uIoc 0 s) : ‖F (Z i t)*probe b ε (Z i t)‖ ≤ C*(Real.exp (-ε*t^2)* Real.exp (|b| *s+ε*s^2)) := by
      have hh := uIoc_subset_uIcc hi; rw [uIcc_of_le hs] at hh
      obtain ⟨h1,h2⟩ := hh
      rw [norm_mul, probed]
      apply mul_le_mul (h.bounded _ (show Z i t∈high from by simp [high,h1])) _ (by positivity) h.rate
      have hx := le_trans (mul_le_mul_of_nonneg_right (le_abs_self b) h1) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (add_le_add hx ?_)) (by positivity); gcongr
    simpa only [sub_zero,abs_of_nonneg hs] using intervalIntegral.norm_integral_le_of_norm_le_const hz
  exact ⟨tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) ht hz),
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) (fun i => show _ ≤ U i by
      simpa [U] using ht (-i)) hz)⟩

lemma same (s b ε : ℝ) (hs : 0 ≤ s) (he : 0 < ε) :
    (∫ t : ℝ, F (Z 0 t)*probe b ε (Z 0 t))=(∫ t : ℝ, F (Z s t)*probe b ε (Z s t)) := by
  let f (z : ℂ) := F z*probe b ε z
  have hh W T : (∫ x in W..T, f (Z 0 x)) - (∫ x in W..T, f (Z s x)) +
      I • (∫ t in 0..s, f (Z t T))-I • (∫ t in 0..s, f (Z t W))=0 := by
    have hC : ContinuousOn f high := h.connects.mul (Continuous.continuousOn (by unfold probe;fun_prop))
    have hF : DifferentiableOn ℂ f loft := h.straight.mul (Differentiable.differentiableOn (by unfold probe;fun_prop))
    have hp := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f (Z 0 W) (Z s T)
      (hC.mono (fun z hz => by
        change 0 ≤ z.im; exact (show z.im∈ Icc 0 s from by simpa only [mem_preimage, level, uIcc_of_le hs] using hz.2).1))
      (hF.mono (fun z hz => by
        change 0 < z.im; exact (show z.im∈ Ioo 0 s from by simpa only [mem_preimage, level,min_eq_left hs,max_eq_right hs] using hz.2).1))
    simp_rw [level,time] at hp; exact hp
  let g (i : ℝ) := ∫ y in 0..s,f (Z y i)
  obtain ⟨hx, hy⟩ := wings h s b ε hs he
  have hx : Tendsto (fun i : ℝ => I • g i) atTop (𝓝 0) := by simpa only [smul_zero] using Tendsto.const_smul hx I
  have hy : Tendsto (fun i : ℝ => I • g (-i)) atTop (𝓝 0) := by simpa only [smul_zero] using Tendsto.const_smul hy I
  have h1 := intervalIntegral_tendsto_integral (finite h 0 b ε le_rfl he) tendsto_neg_atTop_atBot tendsto_id
  have h2 := intervalIntegral_tendsto_integral (finite h s b ε hs he) tendsto_neg_atTop_atBot tendsto_id
  apply sub_eq_zero.mp
  have hp := tendsto_nhds_unique (((h1.sub h2).add hx).sub hy) (tendsto_const_nhds.congr
    (fun i : ℝ => (hh (-i) i).symm))
  simpa only [add_zero,sub_zero] using hp

lemma bound (s b ε : ℝ) (hs : 0 ≤ s) (he : 0 < ε) :
    ‖∫ t : ℝ, F ↑t * probe b ε t‖ ≤ C * (√(Real.pi/ε)*Real.exp (b*s+ε*s^2)) := by
  have hv := same h s b ε hs he; simp_rw [gap_zero] at hv; rw [hv]; apply le_trans
    (norm_integral_le_integral_norm _) _
  rw [← integral_gaussian,← integral_mul_const,← integral_const_mul]
  apply integral_mono (finite h s b ε hs he).norm
    (((integrable_exp_neg_mul_sq he).mul_const _).const_mul _)
  intro x; dsimp only; rw [norm_mul]; conv_rhs => rw [← probed]
  gcongr; exact h.bounded _ (by simp [high,hs])
end YM.Paley
