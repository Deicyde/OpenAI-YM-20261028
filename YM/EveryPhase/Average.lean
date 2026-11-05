import YM.EveryPhase.Polynomials
import YM.EveryPhase.Projection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Time average of vacuum commutator

Saves differentiating spectral integrals (and works without uniform bounds
on generator domain norms). The one-sided unit-interval average of the
antisymmetrization in time still detects low positive frequencies, at
first order in E. Crucial is that its weight can't be negative even at
*high* energies. Thus D(x) a spatial Fourier transform of positive measure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Filter Set Spec Boundary Spectral Mink Probe MeasureTheory Measure
open scoped Topology NNReal ENNReal InnerProductSpace ComplexConjugate Interval

def pulse (t : ℝ) := ∫ x in (0:ℝ)..1, Real.sin (t*x)

lemma pulse_bounded (t) : |pulse t| ≤ 1 := by
  unfold pulse
  rw [intervalIntegral.integral_of_le zero_le_one,← Real.norm_eq_abs]
  have hp := norm_integral_le_of_norm_le (μ:=volume.restrict (Ioc (0:ℝ) 1)) (f:=fun x : ℝ => Real.sin (t*x))
    (g:=fun _ => (1:ℝ)) (integrable_const _) (ae_of_all _ fun x => Real.abs_sin_le_one _)
  simpa using hp

lemma pulse_measurable : Measurable pulse := by
  have h : Measurable (fun p : ℝ × ℝ => Real.sin (p.1*p.2)) := by fun_prop
  have he : pulse = fun t => ∫ x in Ioc (0:ℝ) 1, Real.sin (t*x) := by
    funext; unfold pulse; rw [intervalIntegral.integral_of_le zero_le_one]
  rw [he]; exact (h.stronglyMeasurable.integral_prod_right (ν:=volume.restrict (Ioc (0:ℝ) 1))).measurable

lemma pulse_positive {t : ℝ} (h : 0≤t) : 0≤pulse t := by
  rcases h.eq_or_lt with h|h
  · simp [pulse,←h]
  have he (x) : HasDerivAt (fun x => - Real.cos (t*x)/t) (Real.sin (t*x)) x := by
    convert! (((hasDerivAt_id' x).const_mul t).cos.neg.div_const t) using 1
    field_simp
  unfold pulse; rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => he x)
    ((show Continuous fun x => Real.sin (t*x) from by fun_prop).intervalIntegrable _ _)]
  rw [sub_nonneg]
  gcongr; simp [Real.cos_le_one]

lemma pulse_lower {t : ℝ} (hx : t∈Icc (0:ℝ) 1) : t/Real.pi ≤ pulse t := by
  have ht := hx.2
  have hp := hx.1
  calc
    _ = ∫ x in (0:ℝ)..1, (2/Real.pi*t)*x := by
      rw [intervalIntegral.integral_const_mul, integral_id]; ring
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
        ((show Continuous (fun x : ℝ => (2/Real.pi*t)*x) from by fun_prop).intervalIntegrable ..)
        ((show Continuous (fun u => Real.sin (t*u)) from by fun_prop).intervalIntegrable ..)
      intro x h
      have he := h.1
      have hh : t*x ≤ Real.pi/2 := (mul_le_one₀ ht he h.2).trans (by linarith [Real.two_le_pi])
      rw [mul_assoc]; exact Real.mul_le_sin (mul_nonneg hp he) hh

variable (μ ν : Measure E4)

def up (p : E4) : ℝ≥0 := (pulse (time p)).toNNReal

theorem up_limit (p) : (up p:ℝ) ≤ 1 := by
  unfold up
  rw [Real.coe_toNNReal']; exact max_le ((le_abs_self _).trans (pulse_bounded _)) zero_le_one

lemma up_measurable : Measurable up :=
  continuous_real_toNNReal.measurable.comp (pulse_measurable.comp clock_cont.measurable)

def weighted : Measure E4 := μ.withDensity fun p => ↑(up p)

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
instance : IsFiniteMeasure (weighted μ) := by
  refine ⟨?_⟩; unfold weighted; rw [withDensity_apply _ MeasurableSet.univ]
  apply lt_of_le_of_lt _ (measure_lt_top μ univ)
  rw [← setLIntegral_one]; apply lintegral_mono; intro x
  exact ENNReal.coe_le_one_iff.mpr (up_limit x)

/-! `two`: formula before spatial Fourier testing. Second spectral
measure also contributes with + sign at the opposite spatial frequency. -/

local notation "I" => Complex.I

def oddTest (g : ℝ → ℂ) (t : ℝ) := (g t - g (-t)) / (2*I)

def averaged (g : E4 → ℂ) (x : Space3) := ∫ t in Ioc (0:ℝ) 1,
    oddTest (fun s => g (position x s)) t

lemma intervalChar (μ : Measure E4) [IsFiniteMeasure μ] (x : Space3) :
    Integrable (oddTest (fun t => charFun μ (position x t))) (volume.restrict (Ioc (0:ℝ) 1)) := by
  let f (t : ℝ) := charFun μ (position x t)
  have hx : IntegrableOn f (Ioc (0:ℝ) 1) :=
    (integrable_const (μ:=volume.restrict (Ioc (0:ℝ) 1)) (μ.real univ)).mono'
      (show Measurable f from by unfold f position; fun_prop).aestronglyMeasurable
      (ae_of_all _ fun i => norm_charFun_le _)
  have hk : IntegrableOn (fun t => f (-t)) (Ioc (0:ℝ) 1) :=
    (integrable_const (μ:=volume.restrict (Ioc (0:ℝ) 1)) (μ.real univ)).mono'
      (show Measurable (fun t => f (-t)) from by unfold f position; fun_prop).aestronglyMeasurable
      (ae_of_all _ fun i => norm_charFun_le _)
  exact (hx.sub hk).div_const _

lemma plane_odd (p : E4) (x : Space3) (t : ℝ) :
    oddTest (fun s => plane p (position x s)) t = plane (spatial p) x * ↑(Real.sin (time p*t)) := by
  have he (s : ℝ) : plane p (position x s)= plane (spatial p) x * Complex.exp (↑(time p*s)*I) := by
    unfold plane; rw [Mink.pairing]; simp only [spatial_position,time_position,Complex.ofReal_add,
      add_mul,Complex.exp_add]
  simp only [oddTest]; rw [he,he,Complex.exp_mul_I,Complex.exp_mul_I]
  simp only [mul_neg,Complex.ofReal_neg,Complex.cos_neg,Complex.sin_neg,Complex.ofReal_sin]
  field_simp; ring

lemma one_average (x : Space3) (h : ∀ᵐ p ∂μ, 0≤p timeAxis) :
    averaged (charFun μ) x= charFun ((weighted μ).map spatial) x := by
  let f (s : ℝ) (p : E4) := plane p (position x s)
  let g (s : ℝ) (p : E4) := oddTest (fun t => f t p) s
  have hi (s) : Integrable (f s) μ :=
    (integrable_const (μ:=μ) (1:ℝ)).mono'
      ((show Continuous (f s) from plane_cont.comp (continuous_id.prodMk (continuous_const (y:=position x s)))).aestronglyMeasurable)
      (ae_of_all _ fun p => (plane_norm ..).le)
  have he (p : E4) (s : ℝ) : g s p= plane (spatial p) x*↑(Real.sin (time p*s)) := plane_odd p x s
  let η := volume.restrict (Ioc (0:ℝ) 1)
  haveI : IsFiniteMeasure η := by unfold η; infer_instance
  have hh : Integrable (uncurry g) (η.prod μ) := by
    apply (integrable_const (μ:=η.prod μ) (1:ℝ)).mono'
    · apply Continuous.aestronglyMeasurable; rw [show uncurry g = fun p => plane (spatial p.2) x *
        (↑(Real.sin (time p.2*p.1)):ℂ) from funext fun p => he ..]
      unfold plane; fun_prop
    refine ae_of_all _ fun p => ?_
    change ‖g p.1 p.2‖ ≤ 1; rw [he, norm_mul, Complex.norm_real, plane_norm, one_mul]; exact Real.abs_sin_le_one _
  have hg s : oddTest (fun t => charFun μ (position x t)) s = ∫ p, g s p ∂μ := by
    change ((∫ p, f s p ∂μ)-(∫ p, f (-s) p ∂μ))/(2*I)=_
    rw [← integral_sub (hi _) (hi _),← integral_div]; rfl
  calc
    _ = ∫ s in Ioc (0:ℝ) 1, (∫ p, g s p ∂μ) := by simp_rw [averaged,hg]
    _ = ∫ p, (∫ s in Ioc (0:ℝ) 1, g s p) ∂μ := integral_integral_swap hh
    _ = ∫ p, plane (spatial p) x * (↑(pulse (time p)):ℂ) ∂μ := by
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      simp_rw [he, integral_const_mul, pulse, intervalIntegral.integral_of_le zero_le_one, integral_complex_ofReal]
    _ = _ := by
      rw [charFun_apply, integral_map rest_cont.measurable.aemeasurable (by fun_prop), weighted,
        integral_withDensity_eq_integral_smul up_measurable]
      apply integral_congr_ae
      filter_upwards [h] with p hp
      change _ = (Real.toNNReal _ : ℝ≥0) • plane _ _
      change _ = ((Real.toNNReal (pulse (time p)) : ℝ≥0):ℝ) • plane _ _
      rw [Real.coe_toNNReal _ (pulse_positive (t:=time p) hp), Complex.real_smul,mul_comm]

lemma two_average (x : Space3) (h : ∀ᵐ p ∂μ, 0 ≤ p timeAxis) (hp : ∀ᵐ p ∂ν, 0 ≤ p timeAxis) :
    averaged (fun p => charFun μ p - charFun ν (-p)) x =
      charFun ((weighted μ).map spatial) x + charFun ((weighted ν).map (fun p => -spatial p)) x := by
  have he : charFun ((weighted ν).map (fun p => -spatial p)) x = charFun ((weighted ν).map spatial) (-x) := by
    rw [charFun_apply,charFun_apply,integral_map (by fun_prop) (by fun_prop),
      integral_map rest_cont.measurable.aemeasurable (by fun_prop)]; simp
  rw [he,← one_average μ x h,← one_average ν (-x) hp]
  unfold averaged
  rw [← integral_add (intervalChar μ x) (intervalChar ν (-x))]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  have hh (t) : -(position x t)=position (-x) (-t) := by apply Mink.ext_by <;> simp
  simp only [oddTest]; rw [hh,hh,neg_neg]; ring
end YM.EveryPhase
