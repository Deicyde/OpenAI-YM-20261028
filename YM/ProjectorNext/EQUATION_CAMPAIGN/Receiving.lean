import YM.Next.FOUNDATIONS.SU2
import YM.ProjectorNext.EQUATION_CAMPAIGN.Class
import YM.ProjectorNext.EQUATION_CAMPAIGN.Regularity


set_option warningAsError false

/-!
# Regularity of a finite-regulator signed push in output links

Check the scope of the producer hypotheses: a signal will be regular even globally in
`Y`. It depends on the *same* branch and period. Positivity on the ambient matrix space is
a useful (nonuniform!) extension for an existence check about solely financial finiteness
at one size. Don't try to use such bounds as WM budgets or infer locality from them.

The kernels here are smooth in the remaining variables even when sharp in tag switches,
because we haven't split any sectors upon this check. Keep full summation over choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equations.Finite
open RG Wilson Lattice MeasureTheory Filter Function Set
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n m : Side}
variable (S : StepData n m) (h : S.patch.Branches S.kernel G) (β : ℝ)

def gauss (Q Y : Chart G n) := ∏ b : Edge (Site n),
  (S.penaltyZ β G)⁻¹ * Real.exp (-β*S.kernel.penalty*(1- (Y b * star (Q b)).trace.re / G.repDim))

private lemma gauss_smooth : ContDiff ℝ ∞ (fun x : Chart G n × Chart G n => gauss S β x.2 x.1) := by
  let M : G.Mat →ₗ[ℝ] ℝ := {
    toFun v := v.trace.re / G.repDim
    map_add' x y := by simp [add_div]
    map_smul' c x := by simp; ring }
  unfold gauss
  refine contDiff_prod (fun i _ => ContDiff.mul contDiff_const (ContDiff.exp
    (ContDiff.mul contDiff_const (ContDiff.sub contDiff_const ?_))))
  let Star := (starL' ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap
  exact M.toContinuousLinearMap.contDiff.comp (f:=fun x : Chart G n × Chart G n =>
    x.1 i*Star (x.2 i)) (by fun_prop)

lemma gauss_pos (A B : Chart G n) : 0 < gauss S β A B := Finset.prod_pos fun _ _ =>
  mul_pos (inv_pos.mpr (S.penaltyZ_pos _)) (Real.exp_pos _)



def marginal (U : Config G m) (x : Chart G n) := ∑ t,
    S.likelihood U t * gauss S β (flattenMat (S.prediction U t)) x

include h in
lemma marginal_pos (U : Config G m) (x : Chart G n) : 0<marginal S β U x := by
  obtain ⟨t,hx⟩ : ∃ t, 0<S.likelihood U t := by
    by_contra! he; have ht := S.chosen h U
    have hu := Finset.sum_nonpos (s:=Finset.univ) fun i _ => he i; linarith
  exact Finset.sum_pos' (fun i _ => mul_nonneg (S.likelihood_pos U i) (gauss_pos ..).le) ⟨t,Finset.mem_univ _,mul_pos hx (gauss_pos ..)⟩



variable {𝕜 : Type} [RCLike 𝕜]
variable (f : Config G m → 𝕜) (x : Chart G n) (hi : Integrable f (prior G m))

def allGas := ∫ U, marginal S β U x • f U ∂prior G m

lemma yet (U : Config G n) : S.push β f U = allGas S β f (flattenMat U) := rfl

def pieces (t : S.Choices) (U : Config G m) : 𝕜 := S.likelihood U t • f U

def scaleOnly (t : S.Choices) (V : Config G m) : 𝕜 := pieces S f t V • (gauss S β (flattenMat (S.prediction V t)) x : ℝ)

private lemma scale_at (t : S.Choices) (V : Config G m) :
    scaleOnly S β f x t V = (S.likelihood V t * gauss S β (flattenMat (S.prediction V t)) x) • f V := by
  unfold scaleOnly pieces; simp [Algebra.smul_def, mul_comm, mul_left_comm]

include h hi in
lemma piece_int (t : S.Choices) : Integrable (pieces S f t) (prior G m) := by
  refine hi.bdd_smul 1 (S.likelihood_meas h t |>.aestronglyMeasurable) ?_
  filter_upwards with V
  rw [Real.norm_of_nonneg (S.likelihood_pos ..)]; exact le_trans
    (Finset.single_le_sum (fun i _ => S.likelihood_pos V i) (Finset.mem_univ t)) (S.chosen h V).le

private lemma compressed : IsCompact (Set.range (flattenMat (G:=G) (n:=n))) :=
  isCompact_range (by unfold flattenMat; fun_prop)

include h in
private lemma sampled (t : S.Choices) : AEStronglyMeasurable (fun V : Config G m => flattenMat (S.prediction V t)) (prior G m) :=
  (show Continuous (flattenMat (G:=G) (n:=n)) from by unfold flattenMat; fun_prop).comp_aestronglyMeasurable
    (S.prediction_meas h t).aestronglyMeasurable

private lemma family_smooth : ContDiff ℝ ∞ (fun x : Chart G n × Chart G n =>
    ((gauss S β x.2 x.1 : ℝ) : 𝕜)) := ((algebraMapCLM ℝ 𝕜).contDiff).comp (gauss_smooth S β)

include h hi in
lemma scale_int (t : S.Choices) : Integrable (scaleOnly S β f x t) (prior G m) :=
  compact_weight (piece_int S h f hi t) (sampled S h t) compressed (Eventually.of_forall fun _ => ⟨_,rfl⟩)
    (family_smooth S β (𝕜:=𝕜)).continuous x

private lemma exact_marginal : (fun U => marginal S β U x • f U) = fun V => ∑ t, scaleOnly S β f x t V := by
  funext V; simp only [marginal, scale_at, Finset.sum_smul]

include h hi in
theorem marginals : Integrable (fun U => marginal S β U x • f U) (prior G m) := by
  rw [exact_marginal]; exact integrable_finsetSum _ (fun i _ => scale_int S h β f x hi i)

include h hi in
theorem smooth : ContDiff ℝ ∞ (allGas S β f) := by
  have he x : allGas S β f x = ∑ t, ∫ U, scaleOnly S β f x t U ∂prior G m := by
    unfold allGas; rw [exact_marginal]; exact integral_finsetSum _ (fun i _ => scale_int S h β f _ hi _)
  rw [funext he]
  refine ContDiff.sum fun i _ => contDiff_weighted (piece_int S h f hi i) (sampled S h i)
    compressed (Eventually.of_forall fun _ => ⟨_,rfl⟩) (family_smooth S β)

include h hi in
lemma received : OverEntries (S.push β f) := ⟨_,smooth S h β f hi,funext (yet S β f)⟩

include h in
lemma pos {f : Config G m → ℝ} (hx : Integrable f (prior G m)) (x) (hq : ∀ i, 0<f i) :
    0<allGas S β f x := by
  let F := fun U => marginal S β U x • f U
  have hp (U) : 0<F U := mul_pos (marginal_pos S h β U x) (hq _)
  refine (integral_pos_iff_support_of_nonneg (f:=F) (fun u => (hp u).le) (marginals S h β f x hx)).mpr ?_
  rw [show support F=univ from Set.eq_univ_of_forall (fun x => (hp x).ne')]; simp

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

-- All fine gauges. Coarse gauge is pulled through the actual ancestry lift.
include h in
theorem invariant (P : Config G m → Y) (hg : GaugeInvariant P) (hf : Integrable P (prior G m))
    (hx : ∀ (U : Config G m) V c, S.density β (gauge c U) (gauge (c ∘ S.ratio.embed) V)= S.density β U V) :
    GaugeInvariant (S.push β P) := by
  intro c V
  let q := Function.extend S.ratio.embed c 1
  let F (v : Config G m) := S.density β v (gauge c V) • P v
  have he : Integrable F (prior G m) := StepData.push_slice (S.isKernel h β) _ _ hf
  have hy := prior_gauge q
  have hs := integral_map hy.aemeasurable (f:=F) (by rw [hy.map_eq]; exact he.aestronglyMeasurable)
  rw [hy.map_eq] at hs
  change (∫ U, F U ∂prior G m)=(∫ U, _ ∂prior G m); rw [hs]
  have hh U : F (gauge q U)=S.density β U V • P U := by
    have ht := hx U V q; rw [show q ∘ S.ratio.embed=c from funext fun x => S.ratio.embed_injective.extend_apply ..] at ht
    unfold F; rw [hg, ht]
  simp_rw [hh]
end YM.ProjectorNext.Equations.Finite
