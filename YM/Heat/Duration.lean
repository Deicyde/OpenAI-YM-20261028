import YM.Heat.Lift
import YM.OS.Core

/-!
# Exact damping of spectral measure; undamping operation
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter MeasureTheory Measure Spectral Complex Analysis Boundary Probe
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {H : Hilbert} (a : Axis)

def descent (t : ℝ) (p : E4) : ℝ≥0 := ⟨Real.exp (-t*p a),(Real.exp_pos _).le⟩

lemma measurable (t) : Measurable (descent a t) := by
  unfold descent
  apply Measurable.subtype_mk; fun_prop

def transform (t : ℝ) (μ : Measure E4) : Measure E4 := μ.withDensity fun p => ↑(descent a t p)
lemma stays_put (μ) : transform a 0 μ=μ := by simp [transform,descent]; exact withDensity_one
lemma growth t u μ : transform a t (transform a u μ)=transform a (u+t) μ := by
  unfold transform; rw [← withDensity_mul μ (f := fun p => (↑(descent a u p):ℝ≥0∞)) (g := fun p => (↑(descent a t p):ℝ≥0∞)) (measurable_coe_nnreal_ennreal.comp (measurable a u))
    (measurable_coe_nnreal_ennreal.comp (measurable a t))]
  congr 1; funext p
  simp only [Pi.mul_apply]; rw [← ENNReal.coe_mul]
  congr! 1; apply Subtype.ext
  change Real.exp (-u*p a)*Real.exp (-t*p a)=Real.exp (-(u+t)*p a); rw [← Real.exp_add]; congr 1; ring

variable {a} (S : Semigroup H a)

lemma eitherE (t : ℝ≥0) (p : ℝ) : (S.E t).comp (S.edge p) = (S.edge p).comp (S.E t) := by
  rcases eq_or_ne t 0 with ht|ht
  · rw [ht,S.eZero]; simp
  rw [← S.roots_heat (pos_iff_ne_zero.mpr ht), S.either (dur.mpr (pos_iff_ne_zero.mpr ht)),S.along (dur.mpr (pos_iff_ne_zero.mpr ht))]
lemma overE (t : ℝ≥0) x : (S.E t).comp (S.unit.translation x)=(S.unit.translation x).comp (S.E t) := by
  change (S.E _).comp ((S.edge _).comp _) = _
  rw [← ContinuousLinearMap.comp_assoc, eitherE,ContinuousLinearMap.comp_assoc,S.independent]
  rfl
lemma damp (t : ℝ≥0) (v : H) : S.ℚmeasure.diagonal (S.E t v)=transform a ((t+t:ℝ≥0):ℝ) (S.ℚmeasure.diagonal v) := by
  let m := S.ℚmeasure.diagonal v
  let k := (t+t:ℝ≥0)
  have hv : IsFiniteMeasure (transform a (k:ℝ) m) := by
    refine ⟨?_⟩; unfold transform
    rw [withDensity_apply _ MeasurableSet.univ]
    apply lt_of_le_of_lt _ (measure_lt_top m univ)
    rw [← setLIntegral_one]
    apply lintegral_mono_ae
    have H := S.bright v
    rw [Measure.restrict_univ]
    filter_upwards [H] with y hy
    rw [ENNReal.coe_le_one_iff]
    exact (show Real.exp (-(k:ℝ)*y a) ≤ 1 from Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr k.property) hy))
  change _ = transform a _ m
  letI : IsFiniteMeasure (transform a ((t+t:ℝ≥0):ℝ) m) := hv
  apply Measure.ext_of_charFun
  funext x; rw [S.joint]
  have hx : inner ℂ (S.E t v) (S.unit.translation x (S.E t v))= S.J x v v (Complex.I * ↑(k:ℝ)) := by
    unfold J ray; rw [S.swing, ← ContinuousLinearMap.comp_apply (S.E t), S.overE]
    simp only [mul_re, I_re,zero_mul,I_im,ofReal_im,mul_zero,sub_zero, S.birth, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply (S.E t),← time]
    simp [k,mul_im]
  rw [hx, heat S x v (show _ from by simp [Paley.high]), charFun_apply]
  unfold transform; rw [integral_withDensity_eq_integral_smul (measurable ..)]
  congr! 1; funext p
  dsimp only [plane]
  rw [show (((p a):ℂ)*(I*↑(k:ℝ)))*I= ((↑(-(k:ℝ)*p a)):ℂ) from by push_cast; ring_nf; simp [I_sq], ← Complex.ofReal_exp]
  change cexp (_*I) * _ = (Real.exp _ : ℝ) • cexp (_*I)
  rw [Complex.real_smul,mul_comm]
end YM.OS.Semigroup
