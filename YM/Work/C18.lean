import YM.Bid.Tar
import YM.Org.Twist

set_option autoImplicit false
noncomputable section
namespace YM.Work.C18
open Set Filter MeasureTheory NormedSpace intervalIntegral
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  (u : ℝ → A) (hu : Continuous u) (h0 : u 0 = 1) (ha : ∀ r s, u (r + s) = u r * u s)

include h0 ha hu in
/-- A continuous one-parameter subgroup in a real Banach algebra is an exponential. -/
theorem eq_exponential (r : ℝ) : u r = exp (r • deriv u 0) := by
  let V (t : ℝ) := ∫ s in (0 : ℝ)..t, u s
  have hV t : HasDerivAt V (u t) t := (hu.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • V t) (𝓝[≠] 0) (𝓝 (1 : A)) := by
    simpa [V, h0] using (hV 0).tendsto_slope_zero
  obtain ⟨a, g, hg⟩ : ∃ (a : ℝ) (g : Aˣ), ↑g = a⁻¹ • V a :=
    (hslope.eventually (Units.isOpen.mem_nhds isUnit_one)).exists
  have hVa t : u t * V a = V (t + a) - V t := by
    dsimp only [V]
    rw [integral_interval_sub_left (hu.intervalIntegrable ..) (hu.intervalIntegrable ..)]
    simpa only [ContinuousLinearMap.mul_apply', ← ha, integral_comp_add_left, add_zero] using
      (((ContinuousLinearMap.mul ℝ A (u t)).intervalIntegral_comp_comm
        (a := (0 : ℝ)) (b := a) (μ := volume) (hu.intervalIntegrable ..)).symm :
        u t * (∫ s in (0 : ℝ)..a, u s) = ∫ s in (0 : ℝ)..a, u t * u s)
  have hu_eq : u = fun t => (a⁻¹ • (V (t + a) - V t)) * ↑g⁻¹ := by
    funext t; rw [← hVa, ← mul_smul_comm, ← hg, mul_assoc, g.mul_inv, mul_one]
  have hVd : Differentiable ℝ V := fun t => (hV t).differentiableAt
  have hud : Differentiable ℝ u := hu_eq ▸
    (((hVd.comp (differentiable_id.add_const a)).sub hVd).const_smul a⁻¹).mul_const (↑g⁻¹ : A)
  let x := deriv u 0
  have hdu t : HasDerivAt u (u t * x) t := by
    have he := (hud 0).hasDerivAt
    have het : HasDerivAt u x (t-t) := by simpa [x] using he
    have herr := (het.scomp (h := fun s => s - t) t ((hasDerivAt_id' t).sub_const t)).const_mul (u t)
    simpa [Function.comp_def, ← ha] using herr
  have hz t : HasDerivAt (fun t : ℝ => u t * exp (t • (-x))) 0 t := by
    simpa [mul_assoc] using (hdu t).fun_mul (hasDerivAt_exp_smul_const' (-x) t)
  have he := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt) (fun t => (hz t).deriv) r 0
  have hr := congr_arg (· * exp (r • x)) he
  letI := NormedAlgebra.restrictScalars ℚ ℝ A
  simpa [h0, mul_assoc, ← exp_add_of_commute (Commute.neg_left (Commute.refl (r • x)))] using hr

theorem entire {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    (u : ℝ → B) (hu : Continuous u) (h0 : u 0 = 1) (ha : ∀ r s, u (r+s) = u r * u s) :
    ∃ U : ℂ → B, AnalyticOnNhd ℂ U univ ∧ ∀ r : ℝ, U r = u r := by
  letI := NormedAlgebra.restrictScalars ℝ ℂ B
  let x := deriv u 0
  refine ⟨fun z => exp (z • x), fun z _ => ?_, fun t => ?_⟩
  · exact (exp_analytic (𝕂 := ℂ) (z • x)).comp (f := fun q : ℂ => q • x) ((ContinuousLinearMap.toSpanSingleton ℂ x).analyticAt z)
  change exp ((t : ℂ) • x) = u t
  rw [Complex.coe_smul t x, eq_exponential u hu h0 ha t]

open Mink Boundary Bid

theorem answer : YM.Bid.C18 := by
  intro G L S R h K hK d e
  let E := S.Field d
  let A := E →L[ℂ] E
  let u (t : ℝ) : A := LinearMap.toContinuousLinearMap (K.shell d (e.boost t)).toLinearMap
  have hu : Continuous u := continuous_clm_apply.mpr fun v => (hK.spin d v).comp e.continuousBoost
  have h0 : u 0 = 1 := by
    ext v
    apply S.pin_inj
    change S.pin d (K.shell d (e.boost 0) v) = S.pin d v
    rw [e.boost_start, ← hK.ties, hK.identity]
  have ha r s : u (r+s) = u r * u s := by
    ext v
    apply S.pin_inj
    change S.pin d (K.shell d (e.boost (r+s)) v) =
      S.pin d (K.shell d (e.boost r) (K.shell d (e.boost s) v))
    rw [e.boost_add, ← hK.ties, ← hK.ties, ← hK.ties, hK.representation]
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨U, hU, hr⟩ := entire u hu h0 ha
  refine ⟨U, hU, fun t v => ?_⟩
  change U t v = u t v
  rw [hr]
end YM.Work.C18
