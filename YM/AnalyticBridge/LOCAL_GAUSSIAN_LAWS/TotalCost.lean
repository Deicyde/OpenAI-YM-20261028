import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Density
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.SameQuote
import YM.Next.FREE_KERNELS.Amend
import YM.Next.ROTATIONS.Switch
import YM.Next.SCHEDULE.Pitfalls
import YM.Push.CUTOFF_PROJECTORS.Signed


/-!
# Using the Gaussian exchange even on bounded hard stencils

Local or global tests in counting coordinates, *projections of the same
cloud*, no partial recomputation. TV comparison principle from paying log
factor by a polynomial (don't exponentiate and pay C^volume!). Integrals
include shifts on the old observable needed to read the same active links.
No marked polynomial bounds assumed. Dimensions in caller's actual test
list, so can use if grows slowly compared with e; no inference to whole
density pressure. Independent of choice of χ etc. Applies to any hard
flag arguments if measurable in those coordinates, and bounded WITHOUT
changing domain in the switch. A growth condition replacing boundedness
considered later.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory ProbabilityTheory Matrix
open Bid Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Oriented 
open Next SectorChange SectorChange.Rows SectorChange.Gaussian Wisps
open FreeResolvent
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal

namespace Density
variable {m n α : Type} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
def energy (x : SectorChange.Gaussian.Vec n) := x ⬝ᵥ x


private lemma is_g (A : SectorChange.Gaussian.Table n) : IsGaussian (cloud A) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : n => ℝ)
  change IsGaussian ((multivariateGaussian 0 A).map e.toContinuousLinearMap)
  infer_instance
lemma first_debit (A : SectorChange.Gaussian.Table n) (i : n) : MemLp (fun x : SectorChange.Gaussian.Vec n => x i) 2 (cloud A) := by
  letI := is_g A
  exact IsGaussian.memLp_dual (cloud A) (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : n=>ℝ) i) _ (by norm_num)

lemma meterI (A : SectorChange.Gaussian.Table n) : Integrable energy (cloud A) :=
  integrable_finsetSum _ fun i _ => (by simpa [sq] using (first_debit A i).integrable_sq : Integrable (fun x => x i*x i) (cloud A))

lemma expended (A : SectorChange.Gaussian.Table n) (h : A.PosDef) : (∫ x,energy x ∂cloud A) = ∑ i,A i i := by
  unfold energy dotProduct
  rw [integral_finsetSum]; swap
  · intro i h; simpa [sq] using (first_debit A i).integrable_sq
  apply Finset.sum_congr rfl; intro i hi
  have h := cloud_cov A h i i
  simpa only [ProbabilityTheory.covariance,cloud_center,sub_zero] using h

lemma overspend {C : SectorChange.Gaussian.Table n} (h : C.PosDef) {D : Cost α} {p : n→α} {s A : ℝ}
    (H : D.Schur p p s A C) : (∫ x,energy x ∂cloud C) ≤ Fintype.card n*A := by
  rw [expended C h]; calc
    _ ≤ ∑ _i : n,A := Finset.sum_le_sum fun i _ => (le_abs_self _).trans (by simpa only [Cost.weight_self,one_mul] using (H.rows.weighted i i))
    _ = _ := by simp

/-- `|a-1| ≤ |log a|*(a+1)` avoids exponential-tail dimension issue
when paying a change of covariance analytically. -/
lemma delta {x : ℝ} (hx : 0 < x) : |x-1| ≤ |Real.log x| *x+ |Real.log x| := by
  rcases le_or_gt 1 x with h|h
  · have he : -Real.log x ≤ x⁻¹ - 1 := by simpa using Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    have ht := mul_le_mul_of_nonneg_right he hx.le
    rw [sub_mul, inv_mul_cancel₀ hx.ne', one_mul] at ht
    have hh := Real.log_nonneg h
    rw [abs_of_nonneg hh,abs_of_nonneg (sub_nonneg.mpr h)]; linarith
  have hf := Real.log_le_sub_one_of_pos hx
  have he : Real.log x ≤ 0 := Real.log_nonpos hx.le h.le
  rw [abs_of_nonpos he,abs_of_nonpos (sub_nonpos.mpr h.le)]; nlinarith

/-- Uses *both* variance and mean shifts exactly by reciprocal
change. Sup bound on the observable: only need along those two chart
images, *holding all other variables fixed* in an application. -/
theorem contrast (C A : SectorChange.Gaussian.Table n) (h : C.PosDef) (v : A.PosDef) (u : SectorChange.Gaussian.Vec n)
    (F : SectorChange.Gaussian.Vec n→ℝ) (hF : Measurable F) {ε M P T : ℝ}
    (ht : 0 ≤ M) (_hp : 0 ≤ P) (hT : 0 ≤ T) (he : 0 ≤ ε) (hf : ∀ x, |F x| ≤ M)
    (hb : ∀ y, |Real.log (replace C A u y)| ≤ ε*(P+T*energy y))
    (hx : ∀ x, |Real.log (replace A C (-u) x)| ≤ ε*(P+T*energy x)) {D : ℝ}
    (h₁ : (∫ x,energy x∂cloud C) ≤ D) (h₂ : (∫ x,energy x∂cloud A) ≤ D) :
    |(∫ x,F x∂cloud C) - ∫ y,F (y+u)∂cloud A| ≤ ε*M*(2*P+2*T*D) := by
  let H (y : SectorChange.Gaussian.Vec n) := ε*(P+T*energy y) * M
  let g := replace C A u
  let b y := F (y+u)
  have hI : Integrable F (cloud C) := Integrable.of_bound hF.aestronglyMeasurable M (Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hf))
  obtain ⟨hj,hp'⟩ := exchange C A h v u F
  have hv : Integrable b (cloud A) := Integrable.of_bound (hF.comp (measurable_id.add_const u)).aestronglyMeasurable M
    (Eventually.of_forall fun y => (show |F _| ≤ M from hf _))
  rw [hp',← integral_sub (hj.mp hI) hv,← Real.norm_eq_abs]
  change ‖∫ y,g y * F (y+u)-b y ∂cloud A‖ ≤ _
  let K y := H y + priced C A u H y
  have Hi (C : SectorChange.Gaussian.Table n) : Integrable H (cloud C) :=
    (((integrable_const _).add ((meterI C).const_mul T)).const_mul ε).mul_const M
  have hk : Integrable K (cloud A) := (Hi A).add ((exchange C A h v u H).1.mp (Hi C))
  have hk' (x) : K x = H x + g x * H (x+u) := rfl
  have g₀ x : 0≤g x := (replace_pos C A h v u x).le
  have hg (y : SectorChange.Gaussian.Vec n) : |Real.log (g y)| = |Real.log (replace A C (-u) (y+u))| := by
    have hh := replace_cocycle A C A h (-u) u y
    have ha : replace A A 0 y=1 := by unfold replace chip spice; rw [add_zero,sub_self,Real.exp_zero,div_self (Real.sqrt_ne_zero'.2 v.det_pos),mul_one]
    rw [neg_add_cancel,ha, mul_eq_one_iff_eq_inv₀ ((replace_pos C A h v u y).ne')] at hh -- name
    rw [hh,Real.log_inv,abs_neg]
  refine (norm_integral_le_of_norm_le hk (Eventually.of_forall (fun y => ?_))).trans ?_
  · rw [Real.norm_eq_abs,show g y * F (y+u)-b y=(g y-1)*F (y+u) from (by unfold b; ring),abs_mul]
    have hN := hf (y+u)
    rw [hk']; unfold H
    apply (mul_le_mul (delta (replace_pos _ _ h v u y)) hN (abs_nonneg _) (add_nonneg (mul_nonneg (abs_nonneg _) (g₀ y)) (abs_nonneg _))).trans
    rw [add_mul,add_comm (ε*_*M)]
    refine add_le_add ?_ (mul_le_mul_of_nonneg_right (hb y) ht)
    nth_rw 1 [hg]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hx _) (g₀ _)) ht).trans_eq (by ring)
  unfold K; rw [integral_add (Hi A) ((exchange C A h v u H).1.mp (Hi C)),← (exchange C A h v u H).2]
  change (∫ _,H _∂_)+(∫ _,H _∂_) ≤ _
  unfold H
  simp_rw [integral_mul_const,integral_const_mul, integral_add (integrable_const _) ((meterI _).const_mul T),integral_const,probReal_univ,one_smul]
  simp_rw [integral_const_mul]
  -- calc
  nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₁ hT) (mul_nonneg he ht),
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₂ hT) (mul_nonneg he ht)]
end Density
end YM.AnalyticBridge.LocalGaussianLaws
