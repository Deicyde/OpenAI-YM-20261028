import YM.Distribution.Tests
import YM.Hilbert.Kolmogorov
import YM.Paley.Line

/-!
# Positive finite coefficient must vanish on negative frequency lane

Shift by -b/(2ε), explicit exponent. No infinities in toReal;
diagonal positive. `measure.support` topology. This works for any bounded
analytic. Doesn't discover cone across all maps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Paley
open Function Set Filter MeasureTheory Measure Complex  Topology
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators Real
variable {C : ℝ} {F : ℂ → ℂ}
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (μ : Measure X) [IsFiniteMeasure μ] (x : X → ℝ)

def seed (ε : ℝ) := √(Real.pi/ε)
def shrink (q ε : ℝ) := Real.exp (-q^2/(4*ε))
lemma basis (p b ε : ℝ) (h : 0<ε) :
    (∫ t : ℝ, Complex.exp ((↑(p*t):ℂ)*I) * probe b ε t)=(↑(seed ε*shrink (p-b) ε):ℂ) := by
  let g (T : ℂ) := (Real.pi / (ε:ℂ))^(1/2:ℂ) * Complex.exp (-T^2/(4*(ε:ℂ)))
  have he (p b : ℝ) : (∫ t : ℝ, Complex.exp ((↑(p*t):ℂ)*I) * probe b ε t)=g (↑(p-b)) := by
    unfold probe
    have ht t : Complex.exp ((↑(p*t):ℂ)*I)*probe b ε t=
        Complex.exp (I*(↑(p-b):ℂ)*t)*Complex.exp (-(ε:ℂ)*t^2) := by
      -- t real cast RHS `t^2` ℝ?
      rw [probe, ← Complex.exp_add,← Complex.exp_add]; congr 1; push_cast;ring
    unfold probe at ht
    simp_rw [ht]; exact fourierIntegral_gaussian  (b := (ε:ℂ)) (by simpa using h) (↑(p-b))
  rw [he]
  have hx := he 0 0
  have hv : (Real.pi/(ε:ℂ))^(1/2:ℂ)=↑(seed ε) := by
    suffices he : g 0= ↑(seed ε) by simpa [g] using he
    have ht (t : ℝ) : probe 0 ε t=(↑(Real.exp (-ε*t^2)):ℂ) := by
      unfold probe; rw [Complex.ofReal_exp]; congr 1; push_cast;ring
    simp_rw [zero_mul, ofReal_zero,zero_mul,Complex.exp_zero,one_mul, ht,integral_complex_ofReal,
      integral_gaussian] at hx
    simpa only [sub_zero,ofReal_zero,seed] using hx.symm
  unfold g shrink
  rw [hv]; push_cast
  rfl

/-- Real* test equality. -/
lemma smoothed (hx : Continuous x) (H : ∀ p : ℝ, F p=(∫ y, Complex.exp (↑(x y*p)*I) ∂μ)) (ε b : ℝ) (h : 0 < ε) :
    (∫ t : ℝ, F t * probe b ε t)=(seed ε:ℂ) * ↑(∫ y, shrink (x y-b) ε ∂μ) := by
  simp_rw [H,← integral_mul_const]
  let f := fun (t : ℝ) y => Complex.exp ((↑(x y*t):ℂ)*I) * probe b ε t
  change (∫ t, ∫ y, f t y ∂μ) = _
  rw [integral_integral_swap]
  · unfold f; simp_rw [basis _ _ ε h, ofReal_mul,integral_const_mul, integral_complex_ofReal]
  have hc : Continuous (uncurry f) := continuous_iff_continuousAt.mpr fun p => by unfold f uncurry probe; fun_prop
  -- `R1×μ` integrability on gaussian majorant ν; arbitrary μ finite
  apply ((integrable_exp_neg_mul_sq h).comp_fst (ν := μ)).mono hc.aestronglyMeasurable
  apply ae_of_all; intro i
  change ‖Complex.exp (_*I)*probe b ε ↑(i.1)‖ ≤ ‖Real.exp _‖
  rw [norm_mul, show ‖Complex.exp _‖=(1 : ℝ) from by simp [Complex.norm_exp], ← gap_zero, probed]
  simp

theorem supports (hx : Continuous x) (h : Air F C) (H : ∀ p : ℝ, F p=(∫ y, Complex.exp (↑(x y*p)*I) ∂μ)) :
    μ.support ⊆ {p : X| 0 ≤ x p} := by
  intro p hp
  let b := x p
  by_contra hb'; replace hb := lt_of_not_ge (show ¬0 ≤ b from hb')
  let T := {y : X | (x y-b)^2 < b^2/4}
  have ho : IsOpen T := isOpen_lt ((hx.sub continuous_const).pow _) continuous_const
  have hk : T∈ 𝓝 p := ho.mem_nhds (show (b-b)^2 < _ by nlinarith)
  have he : 0<μ T := (Measure.mem_support_iff_forall p).1 hp _ hk
  let A := μ.real T
  have hr : 0<A := ENNReal.toReal_pos he.ne' (measure_ne_top _ _)
  have hu (ε : ℝ) (hy : 0 < ε) : A ≤ C*Real.exp (-3*b^2/(16*ε)) := by
    let t := -b/(2*ε)
    have ht : 0 ≤ t := (div_pos (neg_pos.mpr hb) (by positivity)).le
    have hg := bound h t b ε ht hy
    let m (y) := shrink (x y-b) ε
    let d := ∫ i, m i ∂μ
    have hr_ := smoothed μ x hx H ε b hy
    rw [hr_,norm_mul] at hg
    have hZ : 0 ≤ d := integral_nonneg fun _ => Real.exp_nonneg _ -- name
    have hv : 0 < seed ε := by unfold seed; positivity
    change ‖(seed ε:ℂ)‖ * ‖(d:ℂ)‖ ≤ _ at hg
    rw [Complex.norm_real,Real.norm_eq_abs, abs_of_pos hv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hZ] at hg
    have hC : d ≤ C*shrink b ε := by
      apply le_of_mul_le_mul_left _ hv
      rw [mul_left_comm (seed ε)] -- adjust
      have hq : b*t+ε*t^2= -b^2/(4*ε) := by unfold t; field_simp;ring
      rw [hq] at hg; exact hg
    let D := Real.exp (-b^2/(16*ε))
    have hD : Integrable m μ := by
      have ht : Continuous m := by unfold m shrink; fun_prop
      apply (integrable_const (μ := μ) (1:ℝ)).mono ht.aestronglyMeasurable
      exact ae_of_all _ fun p => by
        change ‖Real.exp _‖ ≤ ‖(1:ℝ)‖
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_one,Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (x p-b)]) (by positivity)
    have hm : A * D ≤ d := calc
      _ = ∫ x in T, D ∂μ := by simp [A]
      _ ≤ ∫ x in T,m x ∂μ := setIntegral_mono_on (integrable_const _) hD.integrableOn ho.measurableSet fun j hj => by
        apply Real.exp_le_exp.mpr
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [show (x j-b)^2 < _ from hj]
      _ ≤ _ := (setIntegral_le_integral hD (ae_of_all _ fun p => Real.exp_nonneg _))
    apply le_of_mul_le_mul_right _ (Real.exp_pos _ : 0<D); apply hm.trans (hC.trans (le_of_eq ?_))
    unfold shrink; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have ht : Tendsto (fun ε => C* Real.exp (-3*b^2/(16*ε))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    suffices he : Tendsto (fun ε => -3*b^2/(16*ε)) (𝓝[>] 0) atBot from by simpa using (Real.tendsto_exp_atBot.comp he).const_mul C
    have h' : -3*b^2/16 < 0 := by nlinarith
    refine ((tendsto_const_mul_atBot_of_neg h').mpr tendsto_inv_nhdsGT_zero).congr ?_
    intro x; ring
  exact hr.not_ge (ge_of_tendsto ht ((show ∀ᶠ i : ℝ in 𝓝[>] (0:ℝ), 0 < i from self_mem_nhdsWithin).mono fun i hi => hu i hi))
end YM.Paley
