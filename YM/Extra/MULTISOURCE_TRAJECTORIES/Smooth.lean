import YM.Extra.MULTISOURCE_TRAJECTORIES.Stubs
import YM.Work.A15
import YM.Work.C13.Decay

/-!
# Ambient matrix germs and compact-parameter integrals for cylinders

The group output argument of a block push only enters via smooth functions
(no regularity of the branch selection as a function of the integrated
argument asserted). We use global smooth extensions to the REAL ambient matrix
space. Then all finite ordered left derivative prices exist at fixed torus;
no estimate uniform in level, label, or cardinality implied by this argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Wilson RG Lattice Function MeasureTheory Filter Set Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

section Differentiation
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
variable {A B E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {p : α → B} {K : Set B} (hp : AEStronglyMeasurable p μ) (hc : IsCompact K) (hb : ∀ a,p a∈K)
include hp hc hb

omit [NormedSpace ℝ B] [FiniteDimensional ℝ E] in
private lemma integral_cont {F : A × B → E} (h : Continuous F) : Continuous fun x => ∫ a,F (x,p a) ∂μ := by
  apply continuous_iff_continuousAt.mpr; intro x
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod hc).exists_bound_of_continuousOn h.continuousOn
  refine continuousAt_of_dominated (bound:=fun _ => C) (Eventually.of_forall fun y => ?_) ?_ (integrable_const _) (Eventually.of_forall fun a => ?_)
  · exact (h.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hp
  · filter_upwards [Metric.closedBall_mem_nhds x zero_lt_one] with y hy
    exact Eventually.of_forall fun i => hC (y,p i) ⟨hy,hb i⟩
  exact (h.comp (continuous_id.prodMk continuous_const)).continuousAt

lemma integral_contDiff_nat {F : A × B → E} (k : ℕ) (h : ContDiff ℝ k F) :
    ContDiff ℝ k (fun x => ∫ a,F (x,p a) ∂μ) := by
  induction k generalizing E with
  | zero => exact contDiff_zero.mpr (integral_cont hp hc hb h.continuous)
  | succ k ih =>
    let D (q : A × B) := fderiv ℝ (fun x : A => F (x,q.2)) q.1
    have hd : ContDiff ℝ k D := ContDiff.fderiv (m:=↑(k+1 : ℕ))
      (f:=fun (q : A × B) (x : A) => F (x,q.2)) (h.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst)))
        contDiff_fst (by simp)
    have he (x) : HasFDerivAt (fun y => ∫ a,F (y,p a) ∂μ) (∫ a,D (x,p a) ∂μ) x := by
      obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod hc).exists_bound_of_continuousOn hd.continuous.continuousOn
      obtain ⟨C',hC'⟩ := hc.exists_bound_of_continuousOn (f:=fun p => F (x,p))
        (h.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      have hm (y : A) : AEStronglyMeasurable (fun a => F (y,p a)) μ :=
        (h.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hp
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun x a => D (x,p a)) (bound:=fun _ => C)
        (Metric.closedBall_mem_nhds x zero_lt_one) (Eventually.of_forall hm)
        (.of_bound (hm x) C' (Eventually.of_forall fun a => hC' (p a) (hb a)))
        ((hd.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hp)
        (Eventually.of_forall fun a y hy => hC (y,p a) ⟨hy,hb a⟩) (integrable_const _) (Eventually.of_forall fun a y _ => ?_)
      exact ((h.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) y).hasFDerivAt
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv]
    refine ⟨fun y => (he y).differentiableAt,fun h => ?_,?_⟩
    · simp at h
    rw [funext fun x => (he x).fderiv]; exact ih hd

lemma integral_smooth {F : A × B → E} (h : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => ∫ a,F (x,p a) ∂μ) :=
  contDiff_infty.mpr fun k => integral_contDiff_nat hp hc hb k ((contDiff_infty.mp h) k)
end Differentiation

variable {G : Gauge} {n : Side}
abbrev Field (G : Gauge) (n : Side) := Edge (Site n) → G.Mat

def matrixField (U : Config G n) : Field G n := G.mat ∘ U

@[fun_prop] lemma matrixField_cont : Continuous (matrixField (G:=G) (n:=n)) := by unfold matrixField comp; fun_prop

def shift (A : Field G n) (B : Directions G n) : Field G n := fun i => G.mat (G.lieExp (B i)) * A i

lemma shift_smooth : ContDiff ℝ ∞ (uncurry (shift (G:=G) (n:=n))) := by
  apply contDiff_pi.mpr; intro i
  exact ((G.exp_jet.of_le le_top).comp ((contDiff_apply ℝ _ i).comp contDiff_snd)).mul
    ((contDiff_apply ℝ _ i).comp contDiff_fst)



lemma regular_matrix {s : Support n} {f : Field G n → ℂ} (p : BudgetPoint) (h : ContDiff ℝ ∞ f)
    (hg : GaugeInvariant (f ∘ matrixField)) (hl : LocalOn s (f ∘ matrixField)) : p.Regular s (f ∘ matrixField) := by
  have he (U : Config G n) : ContDiffAt ℝ p.order ((f ∘ matrixField) ∘ increment U) 0 :=
    (contDiff_infty.mp (h.comp (shift_smooth.comp (contDiff_const.prodMk contDiff_id))) p.order).contDiffAt
  exact ⟨hl,(h.continuous.comp matrixField_cont).measurable,hg,fun U _ => he U,
    fun U _ A _ hk => Next.Foundations.left_has A hk (he U)⟩

private def jets (f : Field G n → ℂ) : (d : ℕ) → (Fin d → Directions G n) × Field G n → ℂ
  | 0 => fun x => f x.2
  | d+1 => fun x => deriv (fun t : ℝ => jets f d ((fun i => x.1 i.succ),shift x.2 (t • x.1 0))) 0






end YM.Extra.Trajectories
