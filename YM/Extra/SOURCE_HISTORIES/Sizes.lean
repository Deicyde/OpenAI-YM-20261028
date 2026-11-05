import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2
import YM.Work.A15
import YM.Work.B06
import YM.Work.G08

/-! Small currency of the real construction. Use the same `Labels.Frame` and
its l1 `coeffSize` throughout (NOT the instance norm). Countable
superpositions below pay true `RG.SumBudget`.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Extra.Histories
open Lattice Wilson RG Source Labels MeasureTheory Function Filter
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {d : ℕ} {ι κ : Type*}

namespace Size
variable (F : Labels.Frame G d)

lemma smul (x : ℂ) (v : F.Coeff) : F.coeffSize (x • v) = ‖x‖ * F.coeffSize v := by
  unfold Frame.coeffSize
  simp_rw [Pi.smul_apply, norm_smul]
  rw [Finset.mul_sum]

lemma norm_le (v : F.Coeff) : ‖v‖ ≤ F.coeffSize v := by
  apply (pi_norm_le_iff_of_nonneg (Work.G08.size_nonneg F v)).mpr
  intro i
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

lemma le_norm (v : F.Coeff) : F.coeffSize v ≤ (Fintype.card F.Index : ℝ) * ‖v‖ := by
  simpa only [Labels.Frame.coeffSize, nsmul_eq_mul] using
    Pi.sum_norm_apply_le_norm (G := fun _ : F.Index => ℂ) v

lemma add (v w : F.Coeff) : F.coeffSize (v+w) ≤ F.coeffSize v + F.coeffSize w := by
  unfold Frame.coeffSize
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => norm_add_le ..

lemma continuous : Continuous F.coeffSize := by
  unfold Frame.coeffSize
  fun_prop

lemma finite (b : Finset ι) (v : ι → F.Coeff) :
    F.coeffSize (∑ i ∈ b, v i) ≤ ∑ i ∈ b, F.coeffSize (v i) := by
  classical
  induction b using Finset.induction_on with
  | empty => simp [Frame.coeffSize]
  | @insert i b hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (add F ..).trans (add_le_add (le_refl _) ih)

lemma series {v : ι → F.Coeff} (h : Summable fun i => F.coeffSize (v i)) :
    Summable fun i => ‖v i‖ :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_le F _) h

lemma bound {v : ι → F.Coeff} (h : Summable fun i => F.coeffSize (v i)) :
    F.coeffSize (∑' i, v i) ≤ ∑' i, F.coeffSize (v i) := by
  have hx : Tendsto (fun b : Finset ι => F.coeffSize (∑ i ∈ b, v i)) atTop
      (𝓝 (F.coeffSize (∑' i, v i))) := (continuous F).continuousAt.tendsto.comp (series F h).of_norm.hasSum
  exact le_of_tendsto_of_tendsto hx h.hasSum (Eventually.of_forall fun b => finite F b v)

lemma unit_core : F.core F.e0 = 0 := by
  funext i
  change update .. = _
  by_cases hi : i = 0
  · rw [hi,update_self]; rfl
  rw [update_of_ne hi]; exact Pi.single_eq_of_ne hi _

def axis (i : F.Index) : F.Coeff := Pi.single i 1

lemma sum_axes (x : F.Coeff) : ∑ i, x i • axis F i = x := by
  ext j
  simp [axis, Pi.single_apply]

lemma core_axis (i : F.Index) : F.core (axis F i) = if i=0 then 0 else axis F i := by
  split <;> rename_i h
  · rw [h]; exact unit_core F
  ext j
  change update .. = _
  by_cases hj : j = 0
  · subst j; rw [update_self]; simp [axis, Pi.single_eq_of_ne (show 0 ≠ i from Ne.symm h)]
  rw [update_of_ne hj]

lemma size_axis (i : F.Index) : F.coeffSize (axis F i) = 1 := by simp [Frame.coeffSize, axis, Pi.single_apply, apply_ite (‖·‖)]

/-- Unmasked insertion truly includes its global unit. -/
lemma core_plus (x : F.Coeff) : F.core x + x 0 • F.e0 = x := by
  ext i
  change update x 0 0 i + x 0 • (Pi.single (M := fun _ : F.Index => ℂ) 0 1) i = _
  by_cases hi : i = 0
  · simp [hi]
  simp [update_of_ne hi,Pi.single_eq_of_ne hi]

end Size

lemma rem_nonneg {F : Labels.Frame G d} {R : Rep G n} {o : Site n}
    {P : Coefficient F n} {u v : ℝ} (h : P.remBound o R u v) : 0 ≤ v := by
  obtain ⟨a,b,ha,hb,hc,-⟩ := h
  exact (add_nonneg ha hb).trans hc

lemma rem_mono {F : Labels.Frame G d} {R : Rep G n} {o : Site n}
    {P : Coefficient F n} {u v w : ℝ} (h : P.remBound o R u v) (hv : v ≤ w) : P.remBound o R u w := by
  obtain ⟨a,b,h₁,h₂,h₃,H⟩ := h
  exact ⟨a,b,h₁,h₂,h₃.trans hv,H⟩

lemma forcedPos (s : Levels G) (m : ℕ) : 0 < s.clock.forcedAllowance m := Real.exp_pos _

lemma budget_prod {f : ι × κ → ℝ} {c : ι → ℝ}
    (h : ∀ i, SumBudget (fun j => f (i,j)) (c i)) (hh : Summable c) : SumBudget f (∑' i, c i) := by
  have hu : Summable fun i => ∑' j, f (i,j) := .of_nonneg_of_le
    (fun i => tsum_nonneg (h i).1) (fun i => (h i).2.2) hh
  have he (x) : 0 ≤ f x := (h x.1).1 x.2
  have ht : Summable f := (summable_prod_of_nonneg he).mpr ⟨fun i => (h i).2.1,hu⟩
  refine ⟨he,ht,?_⟩
  rw [ht.tsum_prod]
  exact hu.tsum_le_tsum (fun i => (h i).2.2) hh

lemma budget_scale {c r : ℝ} {f : ι → ℝ} (p : SumBudget f c) (hr : 0 ≤ r) :
    SumBudget (fun i => r * f i) (r*c) := by
  refine ⟨fun i => mul_nonneg hr (p.1 i), p.2.1.mul_left _, ?_⟩
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left p.2.2 hr

/-- Pass a really dominated (finite-volume majorant) series through the
ONE shared-choice-density step. No pretending sector predicates commute. -/
theorem push_tsum [Countable ι] {c f : Side} {S : StepData c f} {β : ℝ} {p : ι → Config G f → ℂ}
    (hs : S.IsKernel β G) (h : Dominated p) (hp : ∀ i, Measurable (p i)) (V : Config G c) :
    HasSum (fun i => S.push β (p i) V) (S.push β (fun U => ∑' i, p i U) V) := by
  obtain ⟨q,hq,hb⟩ := h
  have hpn i := Integrable.of_bound ((hp i).aestronglyMeasurable (μ := prior G f)) (q i)
      (Eventually.of_forall (hb i))
  have hsn (i) := StepData.push_slice hs V (p i) (hpn i)
  obtain ⟨B,hB⟩ := hs.bound
  have hz i : (∫ U, ‖S.density β U V • p i U‖ ∂prior G f) ≤ B*q i := by
    rw [show B*q i = ∫ _ : Config G f, B*q i ∂prior G f by rw [integral_const]; simp]
    refine integral_mono (hsn i).norm (integrable_const _) fun U => ?_
    rw [norm_smul,Real.norm_of_nonneg (hs.positive U V)]
    exact mul_le_mul (hB U V) (hb i U) (norm_nonneg _) ((hs.positive U V).trans (hB U V))
  have he := hasSum_integral_of_summable_integral_norm hsn (Summable.of_nonneg_of_le
    (fun i => integral_nonneg (fun U => norm_nonneg _)) hz (hq.mul_left B))
  simpa only [StepData.push, Complex.real_smul, tsum_mul_left] using he

end YM.Extra.Histories
