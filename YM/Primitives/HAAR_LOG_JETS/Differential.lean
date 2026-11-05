import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Contraction
import YM.Work.B16
import YM.Work.G06.Average




/-!
# Actual exponential differential

Series for the differential translated home (color to color,
not ambient matrix-volume density); use the already proved dyadic identity for
`LocalH.coat`, which fixes the convention for left vs right. `projectColor`
is built into `ad`. No assumptions on G beyond `Gauge` here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.HaarLogJets
open Function Filter Set MeasureTheory NormedSpace LocalH
open scoped Topology Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge}

abbrev End (G : Gauge) := G.Color →L[ℝ] G.Color

/-- Generator with the sign for `LocalH.coat`. -/
def back (G : Gauge) : G.Color →L[ℝ] End G :=
  (-LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ G.ad).toContinuousLinearMap

@[simp] theorem back_apply (x y : G.Color) : back G x y = -(G.ad x y) := rfl

theorem exp_back (x y : G.Color) : exp (back G x) y = G.adjoint (G.lieExp x)⁻¹ y := by
  let X := G.colorMat x
  let u (t : ℝ) := exp (t • X)
  let v (t : ℝ) := exp (t • -X)
  let a (t : ℝ) := exp (t • back G x) y
  let f t := u t * G.colorMat (a t) * v t
  have hf (t : ℝ) : HasDerivAt f 0 t := by
    have hu : HasDerivAt u (u t * X) t := hasDerivAt_exp_smul_const ..
    have hv : HasDerivAt v ((-X) * v t) t := hasDerivAt_exp_smul_const' ..
    have ha : HasDerivAt a (back G x (a t)) t := by
      simpa [a] using! (hasDerivAt_exp_smul_const' (back G x) t).clm_apply (hasDerivAt_const t y)
    have hh := ((hu.mul (G.colorMat.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t ha)).mul hv)
    convert! hh using 1
    change 0 = (u t * X * G.colorMat (a t) + u t * G.colorMat (back G x (a t))) * v t + u t * G.colorMat (a t) * (-X * v t)
    rw [back_apply,map_neg,G.colorMat_ad]; change 0 = (u t * X * _ + u t * -(X * _ - _ * X)) * v t + _
    noncomm_ring
  have hh := is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt) (fun t => (hf t).deriv) 1 0
  have ht : G.adjoint (G.lieExp x) (exp (back G x) y) = y := by
    apply G.colorMat_injective
    rw [G.mat_adjoint,Gauge.conjugate,G.mat_lieExp,star_exp,G.colorMat_skew]
    simpa only [f,u,v,a,zero_smul ℝ (back G x),zero_smul, one_smul, exp_zero, one_apply_eq_self,one_mul,mul_one] using (show u 1 * G.colorMat (exp ((1:ℝ) • back G x) y) * v 1 = u 0 * G.colorMat (exp ((0:ℝ) • back G x) y) * v 0 from hh)
  nth_rw 2 [← ht]
  rw [← G.adjoint_mul, inv_mul_cancel, G.adjoint_one]

/-- Scalar series `(exp X - 1)/X` *without* assuming X invertible. -/
def exprel (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] : FormalMultilinearSeries ℝ A A :=
  .ofScalars A fun n => ((n+1).factorial : ℝ)⁻¹

section exprel
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem exprel_radius : (exprel A).radius = ⊤ := by
  apply top_unique
  rw [← expSeries_radius_eq_top ℝ A]
  refine FormalMultilinearSeries.radius_le_of_le fun n => ?_
  rw [expSeries_eq_ofScalars,exprel,FormalMultilinearSeries.ofScalars_norm_eq_mul,FormalMultilinearSeries.ofScalars_norm_eq_mul]
  simp only [norm_inv,Real.norm_natCast]
  gcongr; simp

variable [CompleteSpace A]

theorem exprel_hasFPowerSeriesOnBall : HasFPowerSeriesOnBall (exprel A).sum (exprel A) 0 ⊤ :=
  exprel_radius (A:=A) ▸ (exprel A).hasFPowerSeriesOnBall (by rw [exprel_radius]; simp)

theorem exprel_integral (X : A) : (exprel A).sum X = ∫ t in (0:ℝ)..1, exp (t • X) := by
  let term (n : ℕ) (t : ℝ) := (t^n / (n.factorial : ℝ)) • X^n
  have h : HasSum (fun n => ∫ t in (0:ℝ)..1, term n t) (∫ t in (0:ℝ)..1, exp (t • X)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n (_ : ℝ) => ‖(n.factorial : ℝ)⁻¹ • X^n‖) (fun n => by unfold term; exact (by fun_prop : Continuous _).aestronglyMeasurable)
    · intro n; filter_upwards with t ht
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      unfold term
      simp only [norm_smul, norm_div, norm_pow, Real.norm_of_nonneg ht.1.le, norm_inv]
      grw [ht.2]; · simp [one_div]
      exact ht.1.le
    · filter_upwards with t ht; exact norm_expSeries_summable' X
    · exact intervalIntegrable_const
    filter_upwards with t ht
    simpa only [term, expSeries_apply_eq,smul_pow,smul_smul,div_eq_inv_mul] using! expSeries_hasSum_exp (𝕂:=ℝ) (t • X)
  rw [← h.tsum_eq,FormalMultilinearSeries.sum]
  apply tsum_congr; intro n
  dsimp only [term]
  rw [intervalIntegral.integral_smul_const,intervalIntegral.integral_div,integral_pow,
    exprel, FormalMultilinearSeries.ofScalars_apply_eq,Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp [div_eq_mul_inv, mul_comm]

end exprel

def modelSeries (G : Gauge) : FormalMultilinearSeries ℝ G.Color (End G) :=
  (exprel (End G)).compContinuousLinearMap (back G)

private def model (x : G.Color) := (exprel (End G)).sum (back G x)

private theorem model_series : HasFPowerSeriesOnBall (model (G:=G)) (modelSeries G) 0 ⊤ := by
  have h := exprel_hasFPowerSeriesOnBall (A:=End G)
  rw [← (back G).map_zero] at h
  change HasFPowerSeriesOnBall ((exprel _).sum ∘ back G) _ _ _
  have he := h.compContinuousLinearMap
  rw [ENNReal.top_div_of_ne_top enorm_ne_top] at he; exact he

private theorem model_integral (x : G.Color) : model x = ∫ t in (0:ℝ)..1, exp (back G (t • x)) := by
  rw [model, exprel_integral]; simp_rw [map_smul]

private theorem divided_model (x : G.Color) :
    let b := (1/2:ℝ) • x
    model x = (1/2:ℝ) • (model b + exp (back G b) * model b) := by
  intro b
  letI : IsScalarTower ℝ (End G) (End G) := IsScalarTower.right (R:=ℝ) (A:=End G)
  letI : SMulCommClass ℝ (End G) (End G) := Algebra.to_smulCommClass (R:=ℝ) (A:=End G)
  letI : NormedAlgebra ℚ (End G) := .restrictScalars ℚ ℝ _
  let P (t : ℝ) := exp (back G (t • x))
  have hp : Continuous P := by unfold P; exact exp_continuous.comp ((back G).continuous.comp (continuous_id.smul continuous_const))
  let c : ℝ := 1/2
  have h₁ : (∫ t in (0:ℝ)..1, P (c*t)) = model b := by
    simp_rw [P,mul_comm c,← smul_smul,b,model_integral]; rfl
  have h₂ : (∫ t in (0:ℝ)..1, P (c*t+c)) = P c * model b := by
    have he t : P (c*t+c) = P c * P (c*t) := by
      unfold P
      rw [add_comm,add_smul,map_add,map_smul,map_smul]
      exact exp_add_of_commute (((Commute.refl _).smul_left _).smul_right _)
    simp_rw [he, ← h₁]
    exact ((ContinuousLinearMap.mul ℝ _ (P c)).intervalIntegral_comp_comm ((hp.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1))
  have hs := intervalIntegral.integral_add_adjacent_intervals (hp.intervalIntegrable (μ:=volume) 0 c) (hp.intervalIntegrable c 1)
  have hx := intervalIntegral.smul_integral_comp_mul_left (a:=0) (b:=1) P c
  have hy := intervalIntegral.smul_integral_comp_mul_add (a:=0) (b:=1) P c c
  rw [h₁,mul_one,mul_zero] at hx
  rw [h₂,mul_one,mul_zero, zero_add, show c+c=1 by unfold c; norm_num] at hy
  rw [model_integral]
  change (∫ t in (0:ℝ)..1,P t)= c • (model b + P c * model b)
  rw [smul_add,hx,hy,hs]

theorem coat_smooth (x : G.Color) : ContDiffAt ℝ ω (coat G) x := by
  have he : ContDiff ℝ ω (fun z : G.Color × G.Color => star (G.mat (G.lieExp z.1)) * G.mat (G.lieExp z.2)) := by
    exact (((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff).comp (G.exp_jet.comp contDiff_fst)).mul (G.exp_jet.comp contDiff_snd)
  have ht : ContDiffAt ℝ ω (fun z : G.Color × G.Color => G.plog (star (G.mat (G.lieExp z.1)) * G.mat (G.lieExp z.2))) (x,x) := by
    refine ContDiffAt.comp (g:=G.plog) _ ?_ he.contDiffAt
    simp only [G.mat_star_mul]; exact G.plog_diff
  exact ContDiffAt.fderiv (f:=fun p => move G (G.lieExp p)⁻¹) (g:=id) ht contDiffAt_id (by simp)

/-- The translated differential in the given Lie metric. Entire, including
in abelian and non-injective cases (only use the determinant as a normalized
physical density on the certified chart!). -/
theorem coat_eq (x : G.Color) : coat G x = (exprel (End G)).sum (back G x) := by
  apply ContinuousLinearMap.ext; intro z
  let u (x : G.Color) := coat G x z - model x z
  let c : ℝ := 1/2
  have he (x : G.Color) : u x = c • (u (c • x) + G.adjoint (G.lieExp (c • x))⁻¹ (u (c • x))) := by
    have h := LinearMap.congr_fun (Next.SectorChange.divided_coat x) z
    let b := c • x
    change coat G x z = c • (coat G b z + G.adjoint (G.lieExp b)⁻¹ (coat G b z)) at h
    unfold u
    rw [h, divided_model,smul_apply,add_apply,mul_apply_eq_comp,exp_back, map_sub,← smul_sub]; congr 1; abel
  have hle : ∀ n : ℕ, ‖u x‖ ≤ ‖u (c^n • x)‖ := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      apply ih.trans
      nth_rw 1 [he]; rw [pow_succ',← smul_smul,norm_smul,Real.norm_of_nonneg (by unfold c; norm_num)]
      generalize u (c • c^n • x)=y; generalize (G.lieExp _)⁻¹=g
      have := norm_add_le y (G.adjoint g y); rw [G.norm_adjoint] at this; unfold c; linarith
  have hu : ContinuousAt u 0 := ((coat_smooth 0).continuousAt.clm_apply continuousAt_const).sub
    ((model_series.analyticAt.continuousAt (𝕜:=ℝ)).clm_apply continuousAt_const)
  have hm := ((tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ c by unfold c; norm_num) (show c < 1 by unfold c; norm_num)).smul_const x)
  rw [zero_smul] at hm
  have hh := hu.norm.tendsto.comp hm
  have hh' : Tendsto (fun n : ℕ => ‖u (c^n • x)‖) atTop (𝓝 0) := by
    have ht : model (0:G.Color)=1 := by
      rw [model_integral]; simp
    simpa only [comp_def,u,ht,coat_zero,ContinuousLinearMap.id_apply,one_apply_eq_self,sub_self,norm_zero] using hh
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (ge_of_tendsto hh' (Eventually.of_forall hle)))



theorem coat_integral (x : G.Color) : coat G x = ∫ t in (0:ℝ)..1, exp (back G (t • x)) := by
  rw [coat_eq]; exact model_integral x



end YM.Primitives.HaarLogJets
