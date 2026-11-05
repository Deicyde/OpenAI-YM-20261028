import YM.Next.MULTISOURCE.Chime

/-! analytic kernel as a bounded functional. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Step
open RG Wilson Lattice Function Filter Finset MeasureTheory Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {c f : Side} (S : StepData c f) (h : S.patch.Branches S.kernel G)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def outcome (U : Config G f) : Tests G c →ₗ[ℝ] ℝ where
  toFun x := ∑ i:S.Choices, S.likelihood U i*x (S.prediction U i)
  map_add' := by intro f g; simp_rw [BoundedContinuousFunction.add_apply,mul_add, sum_add_distrib]
  map_smul' := by intro t f; simp [mul_left_comm, Finset.mul_sum]

include h
lemma hopeful (x : Tests G c) (U : Config G f) (he : ∀ u,0<x u) : 0 < outcome S U x := by
  obtain ⟨i,hi⟩ : ∃ i,0 < S.likelihood U i := by
    by_contra! hk
    exact not_lt_of_ge (Finset.sum_nonpos (s:=univ) (fun i _ => hk i)) ((S.chosen h U).symm ▸ zero_lt_one)
  exact (mul_pos hi (he _)).trans_le (single_le_sum (a:=i) (f:=fun t =>
    S.likelihood U t*x (S.prediction U t)) (fun t _ => mul_nonneg (S.likelihood_pos U t) (he _).le) (mem_univ i))
lemma outcome_bound (x : Tests G c) (U : Config G f) : ‖outcome S U x‖ ≤ ‖x‖ := by
  have he t : ‖S.likelihood U t * x (S.prediction U t)‖ ≤ S.likelihood U t*‖x‖ := by
    rw [norm_mul, Real.norm_of_nonneg (S.likelihood_pos ..)]
    exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm ..) (S.likelihood_pos ..)
  apply le_trans (norm_sum_le ..); apply le_trans (sum_le_sum fun i _ => he i)
  rw [← sum_mul, S.chosen h,one_mul]
lemma survives (x : Tests G c) (F : Config G f → V) (he : Integrable F (prior G _)) :
    Integrable (fun U => outcome S U x • F U) (prior G _) := by
  have hh : Measurable fun U => outcome S U x := by
    refine Finset.measurable_fun_sum _ (fun i _ => ?_)
    exact (S.likelihood_meas h i).mul (x.continuous.measurable.comp (S.prediction_meas h i))
  exact he.bdd_smul ‖x‖ hh.aestronglyMeasurable (Eventually.of_forall fun U => outcome_bound S h x U)

section
variable (F : Config G f → V) (he : Integrable F (prior G _))
include he
def assay : Tests G c →ₗ[ℝ] V where
  toFun x := ∫ U, outcome S U x • F U ∂prior G _
  map_add' p q := by simp_rw [map_add,add_smul]; rw [integral_add (survives S h _ F he) (survives S h _ F he)]
  map_smul' x p := by simp_rw [map_smul,smul_assoc x]; rw [integral_smul]; rfl

lemma assay_cost (r : ℝ) (hr : ∀ U, ‖F U‖ ≤ r) (x : Tests G c) : ‖assay S h F he x‖ ≤ r * ‖x‖ := by
  have hx : ∀ U, ‖outcome S U x • F U‖ ≤ r * ‖x‖ := by
    intro U; rw [mul_comm r,norm_smul]; exact mul_le_mul (outcome_bound S h x U) (hr U) (norm_nonneg _) (norm_nonneg _)
  apply le_trans (norm_integral_le_of_norm_le_const (Eventually.of_forall hx)); simp

def appraise {r : ℝ} (hr : ∀ U, ‖F U‖ ≤ r) : Tests G c →L[ℝ] V :=
    (assay S h F he).mkContinuous r (assay_cost S h F he r hr)
lemma appraisal {r : ℝ} (hr : ∀ U, ‖F U‖ ≤ r) : ‖appraise S h F he hr‖ ≤ r :=
    (assay S h F he).mkContinuous_norm_le ((norm_nonneg _).trans (hr 1)) _
lemma kernel_push {r : ℝ} (hr : ∀ U, ‖F U‖ ≤ r) (U : Config G c) (β : ℝ) :
    S.push β F U=appraise S h F he hr (curve S β (showU U)) := by
  change _= ∫ V : Config G f, (∑ t:S.Choices,_ * curve S β (showU U) (S.prediction V t)) • F V ∂prior G _
  simp_rw [costs]; rfl
end
end YM.Multi.Step
