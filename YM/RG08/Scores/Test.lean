import YM.Planned.PRIMARY_INTEGRAL_295.Paint
import Mathlib.Topology.ContinuousMap.Compact

/-!
# One physical test mark and its exact addresses for the formal Wilson programs

Real multilinear coordinates. Keep tests through **all their D derivatives**,
not just finitely many numbers at the consolidation point. No wrap in formal
cells. `R=1/2` is the exact centered cell convention; allow fixed larger cubes
as well for auxiliary tests. Gauge field directions remain separate.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Scores
open Function Set Filter
open scoped ContDiff Topology BigOperators

variable (D : ℕ) (R : ℝ)
def examinable (R : ℝ) : Set E4 := {x | ∀ i, ‖x i‖ ≤ R}
lemma grounds : IsCompact (examinable R) ∧ Convex ℝ (examinable R) := by
  let e := PiLp.continuousLinearEquiv (p:=2) ℝ (fun _ : Axis => ℝ)
  by_cases h : 0 ≤ R
  · have hh : examinable R=e ⁻¹' Metric.closedBall 0 R := by
      ext x
      rw [mem_preimage, Metric.mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg h]; rfl
    rw [hh]; exact ⟨(e.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall ..)),(convex_closedBall ..).linear_preimage e.toLinearMap⟩
  have he : examinable R=∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx => h ((norm_nonneg (x (0:Axis))).trans (hx 0))
  rw [he]; exact ⟨isCompact_empty,convex_empty⟩

lemma affordable : ∃ χ:ℝ, 1≤χ ∧ ∀ x ∈ examinable R, ‖x‖≤χ := by
  obtain ⟨b,hb⟩:= ((grounds R).1.image continuous_norm).bddAbove
  exact ⟨max 1 b,le_max_left ..,fun x hx=>(hb ⟨x,hx,rfl⟩).trans (le_max_right ..)⟩

abbrev Close (R : ℝ) := ↥(examinable R)
instance instCompactClose : CompactSpace (Close R) := isCompact_iff_compactSpace.mp (grounds R).1
def Sheet (D : ℕ) := Σ k : Fin (D+1), (Fin k.val→Axis)
instance : Fintype (Sheet D) := by unfold Sheet; infer_instance
instance : TopologicalSpace (Sheet D) := ⊥
instance : DiscreteTopology (Sheet D) := ⟨rfl⟩

abbrev Board := C(Close R, ℝ)

def verse : Submodule ℝ (E4→ℝ) where
  carrier := {f | ContDiff ℝ D f}
  zero_mem' := (show ContDiff ℝ D (fun _ : E4 => (0:ℝ)) from contDiff_const)
  add_mem' := by
    rintro a b (ha : ContDiff ℝ D a) (hb : ContDiff ℝ D b); exact ha.add hb
  smul_mem' := by
    rintro c x (hx : ContDiff ℝ D x); exact hx.const_smul c

abbrev Exam := ↥(verse D)
lemma score (φ : Exam D) : ContDiff ℝ D φ.val := φ.property

def mark (φ : Exam D) (k : Sheet D) : Board R := by
  rcases k with ⟨⟨i,hi⟩,b⟩
  refine ⟨fun x => iteratedFDeriv ℝ i φ.val x.val (basis ∘ b),?_⟩
  exact ((ContinuousMultilinearMap.apply ℝ _ ℝ _).continuous.comp
    ((ContDiff.continuous_iteratedFDeriv (Nat.cast_le.mpr (by omega)) φ.property).comp continuous_subtype_val))
lemma mark_read {i : ℕ} (h : i ≤ D) (x : Close R) (φ : Exam D) (v : Fin i → Axis) :
    mark D R φ (⟨⟨i,by omega⟩,v⟩ : Sheet D) x=iteratedFDeriv ℝ i φ.val x.val (basis ∘ v) := rfl

def hall : Exam D →ₗ[ℝ] (Sheet D → Board R) where
  toFun := mark D R
  map_add' φ ψ := by
    ext1 i; refine ContinuousMap.ext (fun x => ?_)
    rcases i with ⟨⟨i,hi⟩,a⟩
    have hφ : ContDiffAt ℝ i φ.val x.val := ((ContDiff.of_le (score D φ) (Nat.cast_le.mpr (by omega)))).contDiffAt
    have hψ : ContDiffAt ℝ i ψ.val x.val := ((ContDiff.of_le (score D ψ) (Nat.cast_le.mpr (by omega)))).contDiffAt
    change (iteratedFDeriv ℝ i (φ.val+ψ.val) x.val) (basis ∘ a) = _
    rw [iteratedFDeriv_add_apply hφ hψ]; rfl
  map_smul' c φ := by
    ext1 i; refine ContinuousMap.ext (fun x => ?_)
    rcases i with ⟨⟨i,hi⟩,a⟩
    have hφ : ContDiffAt ℝ i φ.val x.val := ((ContDiff.of_le (score D φ) (Nat.cast_le.mpr (by omega)))).contDiffAt
    change (iteratedFDeriv ℝ i (c•φ.val) x.val) (basis ∘ a) = _
    rw [iteratedFDeriv_const_smul_apply hφ]; rfl
abbrev Sight := ↥(hall D R).range
instance : NormedAddCommGroup (Sight D R) := inferInstance
instance : NormedSpace ℝ (Sight D R) := inferInstance
def sheet : Exam D →ₗ[ℝ] Sight D R := (hall D R).rangeRestrict
lemma doors : Surjective (sheet D R) := by
  rintro ⟨x,m,h⟩; exact ⟨m,Subtype.ext h⟩
abbrev Voice := Sight D R →L[ℝ] ℝ
-- Make budget comparisons symmetric. Voice needn't be realized by values alone.
def utter (x : Close R) (i : Sheet D) : Voice D R :=
  (ContinuousMap.evalCLM ℝ x).comp ((ContinuousLinearMap.proj i).comp ((hall D R).range.subtypeL))
lemma whisper (x : Close R) (i : Sheet D) (φ : Exam D) : utter D R x i (sheet D R φ)=mark D R φ i x := rfl
lemma norm_mark (x : Close R) (i : Sheet D) (g : Sight D R) : ‖utter D R x i g‖ ≤ ‖g‖ :=
  (ContinuousMap.norm_coe_le_norm (g.val i) x).trans (norm_le_pi_norm g.val i)
lemma halt (x : Close R) (i : Sheet D) : ‖utter D R x i‖≤1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g=>by
  rw [one_mul]; exact norm_mark D R x i g
lemma bound (φ : Exam D) {M : ℝ} (h : 0≤M) : ‖sheet D R φ‖ ≤ M ↔ ∀ i x, ‖mark D R φ i x‖ ≤ M := by
  refine ⟨fun he i x => (norm_mark D R x i (sheet D R φ)).trans he, fun he => ?_⟩
  change ‖hall D R φ‖ ≤ M; exact (pi_norm_le_iff_of_nonneg h).mpr fun i=>(ContinuousMap.norm_le _ h).mpr (he i)

lemma limit_basis (k : ℕ) (A : E4 [×k]→L[ℝ] ℝ) {M : ℝ} (hM : 0≤M)
    (h : ∀ v:Fin k → Axis, ‖A (basis ∘ v)‖ ≤ M) : ‖A‖ ≤ (4:ℝ)^k*M := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity); intro x
  have hv (a : Fin k) (i : Axis) : ‖x a i‖≤ ‖x a‖ := by
    exact PiLp.norm_apply_le ..
  have he : x = fun a => ∑ i : Axis, (x a i) • basis i := by ext a i; simp
  conv_lhs => rw [he,A.map_sum (fun a i => (x a i) • basis i)]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _ : Fin k→Axis, M * ∏ i, ‖x i‖ := Finset.sum_le_sum (fun i _ => by
          rw [A.map_smul_univ (fun a => x a (i a)) (fun a => basis (i a)),norm_smul,norm_prod,mul_comm]; exact mul_le_mul (h i) (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=>hv j _)) (by positivity) hM)
    _ = _ := by simp [Axis,mul_assoc]
lemma jet_budget (φ : Exam D) (k : ℕ) (hk:k≤D) (x : Close R) :
    ‖iteratedFDeriv ℝ k φ.val x.val‖ ≤ (4:ℝ)^k * ‖sheet D R φ‖ := limit_basis k _ (norm_nonneg _) fun i => by
      rw [← mark_read D R hk]; exact (bound D R φ (norm_nonneg _)).mp le_rfl _ _

-- Costed factoring through genuine evaluated kernels.
variable {E F G M : Type*} [AddCommGroup M] [Module ℝ M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma port (q : M →ₗ[ℝ] E) (hq : Surjective q) (f : M →ₗ[ℝ] F) {C : ℝ} (hC : 0≤C)
    (h : ∀ m, ‖f m‖ ≤ C * ‖q m‖) : ∃ A : E →L[ℝ] F, ‖A‖≤C ∧ A.toLinearMap.comp q=f := by
  obtain ⟨w,hw⟩:= q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have he (x) : q (w x)=x := LinearMap.congr_fun hw x
  have hb x : ‖f.comp w x‖≤C*‖x‖ := by simpa [he] using h (w x)
  let A := (f.comp w).mkContinuous C hb
  refine ⟨A, LinearMap.mkContinuous_norm_le _ hC hb,LinearMap.ext fun m=> ?_⟩
  have hX := h (w (q m)-m); rw [map_sub f,map_sub q,he, sub_self,norm_zero,mul_zero] at hX
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hX)
end YM.RG08.Scores
