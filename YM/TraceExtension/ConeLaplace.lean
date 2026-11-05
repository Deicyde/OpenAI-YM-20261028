import YM.TraceExtension.PolynomialGrowth
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! Candidate forward-cone measure in the specified Lebesgue convention, and its
Laplace transform. Nonnegative integrals throughout where we must not assume
finiteness; justify before using real mass. -/

set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Measure Metric Mink Boundary
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Interval

lemma future {u : E4} (hu : u ∈ inside) : ∃ (s : ℝ), 0<s ∧ ∃ g : Lorentz, g.act (s • basis timeAxis) = u := by
    obtain ⟨ht,hm⟩ := (strict_self _).1 hu
    by_cases he : spatial u=0
    · refine ⟨time u,ht,1,ext_by ?_ ?_⟩ <;> simp [he]
    let x := ‖spatial u‖
    have hx : 0<x := norm_pos_iff.mpr he
    let s := Real.sqrt (m u)
    have hs : 0 < s := Real.sqrt_pos.mpr hm
    let R : Ray := ⟨x⁻¹ • spatial u,by rw [norm_smul,Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),inv_mul_cancel₀ hx.ne']⟩
    obtain ⟨t,h⟩ := Real.sinh_surjective (x/s)
    refine ⟨s,hs,R.boost t,?_⟩; apply ext_by
    · rw [Ray.boost_at,Ray.newSpace]; simp only [rest_mul,roll_space,smul_zero,clock_mul,roll_clock,mul_one, Ray.along,inner_zero_left,mul_zero,add_zero,zero_add]
      change (Real.sinh t * s) • (x⁻¹ • spatial u)=_
      rw [h,div_mul_cancel₀ _ hs.ne',smul_smul,mul_inv_cancel₀ hx.ne',one_smul]
    rw [Ray.boost_at,Ray.newClock]
    simp only [clock_mul,roll_clock,mul_one,Ray.along,rest_mul,roll_space,smul_zero,inner_zero_left,mul_zero,add_zero]
    have hq : s^2=time u^2-x^2 := Real.sq_sqrt hm.le
    apply (sq_eq_sq₀ (mul_nonneg (Real.cosh_pos _).le hs.le) ht.le).mp
    have hp : Real.sinh t*s=x := by rw [h,div_mul_cancel₀ _ hs.ne']
    have hz := Real.cosh_sq_sub_sinh_sq t
    rw [mul_pow,show Real.cosh t^2=1+Real.sinh t^2 by linarith,add_mul,← mul_pow (Real.sinh t),hp]
    linarith

/-- Positive measure e^{-p.u} dμ(p). -/
def lagWeight (u p : E4) : ℝ≥0 := ⟨Real.exp (-(inner ℝ u p)),Real.exp_nonneg _⟩
def lag (μ : Measure E4) (u : E4) := μ.withDensity (fun p => (lagWeight u p : ℝ≥0∞))
@[fun_prop] lemma lagWeight_cont (u : E4) : Continuous (lagWeight u) := Continuous.subtype_mk
    (f:=fun p:E4 => Real.exp (-(inner ℝ u p))) (by fun_prop) _
lemma lagWeight_meas (u : E4) : Measurable (fun p => (lagWeight u p : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp (lagWeight_cont u).measurable

lemma time_lag (s : ℝ) (μ : Measure E4) : lag μ (s • basis timeAxis) = OS.Semigroup.transform timeAxis s μ := by
    unfold lag OS.Semigroup.transform; congr 1
    ext p; simp [lagWeight, OS.Semigroup.descent,real_inner_smul_left]
lemma lag_invariant (μ : Measure E4) (hb : ∀ g : Lorentz, μ.map g.act = μ) (g : Lorentz) (u : E4) :
    lag μ (g.act u) univ=lag μ u univ := by
    unfold lag; rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ]
    simp only [restrict_univ]
    conv_lhs => rw [← hb g.dual]
    rw [lintegral_map (lagWeight_meas _) g.dual.act.continuous.measurable]
    simp only [lagWeight,Lorentz.dual_sent]

def coneMeasure (A : ℝ) : Measure E4 := (volume.restrict cone).withDensity fun x => ENNReal.ofReal (A/(1536*Real.pi)*(m x)^2)
lemma coneMeasure_cone (A : ℝ) : coneMeasure A coneᶜ=0 := (withDensity_absolutelyContinuous ..) (by rw [restrict_apply closed_cone.measurableSet.compl]; simp)
lemma coneMeasure_invariant (A : ℝ) (g : Lorentz) : (coneMeasure A).map g.act=coneMeasure A := by
    ext s hs
    let f := fun x : E4 => ENNReal.ofReal (A/(1536*Real.pi)*(m x)^2)
    have hm := g.act.continuous.measurable; have hv := g.preserves
    have he : Measure.map g.act volume = volume := hv.map_eq
    change ((volume.restrict cone).withDensity f).map g.act s = _
    rw [Measure.map_apply hm hs, coneMeasure,withDensity_apply _ (hm hs),withDensity_apply _ hs,
        restrict_restrict (hm hs),restrict_restrict hs]
    change (∫⁻ x in _, f x) = ∫⁻ x in s∩cone, f x
    conv_rhs => rw [← he]
    have ht : Measurable f := by unfold f; exact Measurable.ennreal_ofReal (by fun_prop)
    rw [setLIntegral_map (hs.inter closed_cone.measurableSet) ht hm]
    simp only [f,g.keeps,preimage_inter, show g.act ⁻¹' cone = cone from Set.ext (fun x => g.keepsCone x)]

private lemma radial_circle {t : ℝ} (ht : 0 ≤ t) :
    ∫ y : Space3 in closedBall 0 t,(t^2-‖y‖^2)^2 = 4 * Real.pi * (8/105) * t^7 := by
    let f (r : ℝ) := (Iic t).indicator (fun r : ℝ => (t^2-r^2)^2) r
    let c := volume (α := Space3)
    have he : (∫ y : Space3 in closedBall 0 t,(t^2-‖y‖^2)^2) = ∫ y : Space3, f ‖y‖ := by
        rw [← integral_indicator (f:=fun y:Space3 => _) measurableSet_closedBall]
        congr! 1; ext x; simp [f,Set.indicator]
    rw [he,MeasureTheory.integral_fun_norm_addHaar]
    have hp : Module.finrank ℝ Space3=3 := finrank_euclideanSpace_fin
    have hc : c.real (ball 0 1) = Real.pi * 4 / 3 := by
        unfold Measure.real c; rw [EuclideanSpace.volume_ball_fin_three]; simp [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
    rw [hp,hc]; push_cast; norm_num
    rw [show (fun y : ℝ => y^2*f y) = (Iic t).indicator (fun y => y^2 * (t^2-y^2)^2) by
        ext y; by_cases h:y∈Iic t <;> simp [f,h], setIntegral_indicator measurableSet_Iic]
    rw [Ioi_inter_Iic, ← intervalIntegral.integral_of_le ht, show (fun y : ℝ => y^2*(t^2-y^2)^2) = (fun y => t^4*y^2-2*t^2*y^4+y^6) by funext; ring]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,integral_pow,integral_pow,integral_pow]
    · norm_num; ring
    all_goals apply Continuous.intervalIntegrable ; fun_prop

private lemma gamma_seven {s : ℝ} (hs : 0<s) : ∫ t : ℝ in Ioi 0,t^7 * Real.exp (-s*t) = 5040 * s⁻¹ ^ 8 := by
    have hQ (x : ℝ) : x ^ ((8:ℝ)-1) = x^7 := by norm_num
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=8) (by norm_num) hs
    have he : Real.Gamma 8=5040 := by
        have hu := Real.Gamma_nat_eq_factorial 7
        norm_num [Nat.factorial] at *
    simp_rw [← neg_mul,hQ] at h; rw [h,he]; norm_num; ring

private lemma cone_tonelli (a s : ℝ) (ha : 0 ≤ a) (hs : 0<s) :
    (∫⁻ x in cone, ENNReal.ofReal (a* m x ^2 * Real.exp (-s*time x))) = ENNReal.ofReal (1536 * Real.pi * a * s⁻¹ ^ 8) := by
    let f (u : E4) := ENNReal.ofReal (a*m u^2*Real.exp (-s*time u))
    have hf : Measurable f := by unfold f; fun_prop
    let g := fun q : Space3 × ℝ => cone.indicator f (divide.symm q)
    have hg : Measurable g := (hf.indicator closed_cone.measurableSet).comp divide.symm.continuous.measurable
    rw [show (∫⁻ x in cone,_)= ∫⁻ x in cone, f x from rfl, ← lintegral_indicator closed_cone.measurableSet]
    have htu : cone.indicator f = fun x => g (divide x) := by ext1; unfold g; simp
    let b := 4 * Real.pi * (8/105)
    have hb : 0 < b := by unfold b; positivity
    have hr (t : ℝ) : (∫⁻ x : Space3,g (x,t)) = (Ioi 0).indicator (fun t => ENNReal.ofReal (b*a*(t^7*Real.exp (-s*t)))) t := by
        let K := closedBall (0:Space3) t
        let v (x : Space3) := a * (t^2-‖x‖^2)^2 * Real.exp (-s*t)
        have he : (fun x : Space3 => g (x,t))=K.indicator (fun x => ENNReal.ofReal (v x)) := by
            ext x; simp [g,K,Set.indicator,cone,f,v,m]
        rw [he, lintegral_indicator isClosed_closedBall.measurableSet]
        have hv : IntegrableOn v K := ContinuousOn.integrableOn_compact (isCompact_closedBall ..) (Continuous.continuousOn (by unfold v; fun_prop))
        rw [← ofReal_integral_eq_lintegral_ofReal hv (ae_of_all _ fun x => (by dsimp [v]; positivity : 0 ≤ v x))]
        rcases lt_or_ge t 0 with hh|hh
        · simp [K, closedBall_eq_empty.mpr hh,Set.indicator,not_lt_of_ge hh.le]
        have he' : (∫ x in K, v x) = b*a*(t^7*Real.exp (-s*t)) := by
            unfold v K
            rw [integral_mul_const,integral_const_mul, radial_circle hh]; dsimp [b]; ring
        rw [he']; rcases eq_or_lt_of_le hh with hz|hl
        · rw [← hz]; simp
        simp [Set.indicator,hl]
    change (∫⁻ x,cone.indicator f x)=_
    have hp := volume_divide.lintegral_comp hg
    rw [htu,hp]; rw [show (volume : Measure (Space3 × ℝ))=volume.prod volume from rfl, lintegral_prod_symm _ hg.aemeasurable]
    simp_rw [hr]; rw [lintegral_indicator measurableSet_Ioi,← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_const_mul, gamma_seven hs]; congr 1; unfold b; ring
    · apply Integrable.const_mul
      by_contra h
      have hx := integral_undef h; rw [gamma_seven hs] at hx; exact (by positivity : 0<5040*s⁻¹^8).ne' hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; change 0 ≤ b*a*_; have h : 0<x:=hx; positivity

lemma cone_laplace (A s : ℝ) (ha : 0 ≤ A) (hs : 0<s) :
    lag (coneMeasure A) (s • basis timeAxis) univ=ENNReal.ofReal (A*s⁻¹ ^ 8) := by
    let a := A/(1536*Real.pi)
    have hf : 0 ≤ a := by unfold a; positivity
    rw [lag,withDensity_apply _ MeasurableSet.univ, restrict_univ,coneMeasure,lintegral_withDensity_eq_lintegral_mul _ (_:Measurable _) (lagWeight_meas ..)]
    swap
    · exact Measurable.ennreal_ofReal (by fun_prop)
    convert cone_tonelli a s hf hs using 1
    · apply lintegral_congr; intro x
      rw [Pi.mul_apply, ENNReal.ofReal_mul (by positivity : 0 ≤ a * m x ^2)]
      congr 1
      have he : inner ℝ (s • basis timeAxis) x = s*time x := by rw [real_inner_smul_left,basis_inner]; rfl
      rw [← ENNReal.ofReal_coe_nnreal]; congr 1; change Real.exp (-(inner ℝ (s • basis timeAxis) x)) = _; rw [he,neg_mul]
    congr 1; dsimp only [a]; field_simp
end YM.TraceExtension
