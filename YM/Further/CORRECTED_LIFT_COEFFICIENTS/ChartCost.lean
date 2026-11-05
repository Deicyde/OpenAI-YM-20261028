import YM.Next.EXTRACTION.Detector
import YM.Next.FOUNDATIONS.TestBounds
import YM.Push.CORRECTED_COLUMNS.Program
import YM.Push.CUTOFF_PROJECTORS.Equations

/-!
# The derivative charges through changing from actual old-threshold charts

Instance of  arithmetic for the calibration jets at the base point.
No factor scaling with the periodic volume from the mixed derivatives.
Identity point only, don't infer a remainder estimate on interpolations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Filter Function Tensor Lattice Wilson RG Next.Extract Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side} {X : Support n} {P : BudgetPoint} {o : Site n} {f : Config G n → ℂ}

namespace Costs
abbrev SymVec (i : ℕ) := Tensor.T (Fin i → ℝ) ℂ i
private def Price (i : ℕ) : Submodule ℂ (SymVec i) where
  carrier := {A | Tensor.Sym A}
  add_mem' := by
    intro a b ha hb
    exact fun v s => by rw [add_apply,add_apply,show a _ = _ from (show Tensor.Sym a from ha) v s, show b _ = _ from (show Tensor.Sym b from hb) v s]
  smul_mem' := fun c a ha v s => by rw [smul_apply,smul_apply,(show Tensor.Sym a from ha) v s]
  zero_mem' := fun _ _ => rfl

-- Restrict to Fin i sized spaces even though v may have all coordinates at n alive
-- (finite-detector version of the mixed polarization idea of FOUNDATIONS).
private lemma diagonal_cost (i : ℕ) (w : (Fin i → ℝ) → ℝ) (hw : ∀ a, 0 ≤ w a) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ A : SymVec i, Tensor.Sym A → ∀ r : ℝ, 0 ≤ r →
      (∀ x, ‖Tensor.diagonal A x‖ ≤ w x*r) → ‖A (fun j => Pi.single j 1)‖ ≤ c*r := by
  classical
  letI : FiniteDimensional ℂ (SymVec i) := Module.Finite.of_restrictScalars_finite ℝ ℂ _
  let L (x : Fin i → ℝ) : Price i →L[ℂ] ℂ := LinearMap.toContinuousLinearMap {
    toFun A := Tensor.diagonal A.val x
    map_smul' a A := rfl
    map_add' A B := rfl }
  have he (x : Price i) (_ : (ContinuousLinearMap.id ℂ _) x=x) (h : ∀ j,L j x=0) : x=0 :=
    Subtype.ext (Tensor.ext_diag x.val 0 x.property (fun _ _ => rfl) (funext h))
  obtain ⟨I,s,hs,H⟩ := finite_detectors (V:=Price i) (ι:=Fin i → ℝ) (ContinuousLinearMap.id ℂ (Price i)) L he
  let q (k : Fin i) : Fin i → ℝ := (Pi.single k (1:ℝ))
  let z := ∑ j∈I, w j; let W := ∏ k : Fin i, ‖q k‖
  have hW : 0 ≤ W := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hz : 0 ≤ z := Finset.sum_nonneg fun i _ => hw i
  refine ⟨z/s*W,by positivity,fun A hA r hr hj => ?_⟩
  have hv : s*‖A‖ ≤ z*r := by
    unfold z; rw [Finset.sum_mul]
    apply le_trans ?_ (Finset.sum_le_sum (s:=I) (fun j _ => hj j))
    let B : Price i := ⟨A,hA⟩
    have h := H B
    rw [ContinuousLinearMap.id_apply, sub_self, @norm_zero (Price i) _,zero_add] at h; exact h
  apply (A.le_opNorm q).trans
  change ‖A‖*W ≤ _
  have h : ‖A‖ ≤ z/s*r := by apply (le_div_iff₀ hs).2 (show ‖A‖*s ≤ z*r by linarith) |>.trans_eq; ring
  exact (mul_le_mul_of_nonneg_right h hW).trans_eq (by ring)

def scaledFun (P : BudgetPoint) (f : Config G n → ℂ) : Directions G n → ℂ :=
  (f ∘ increment 1) ∘ fun y => P.threshold • y

lemma scaled_nice (h : P.Regular X f) (i : ℕ) (hi : i ≤ P.order) :
    ContDiffAt ℝ i (scaledFun P f) 0 := by
  let z : Directions G n →L[ℝ] Directions G n := P.threshold • ContinuousLinearMap.id ℝ _
  apply ContDiffAt.comp (g:=f ∘ increment 1) (f:=z) _ _ z.contDiff.contDiffAt
  rw [map_zero]; exact (h.smooth _ (one_healthy _ _ P.threshold_pos.le)).of_le (Nat.cast_le.mpr hi)

private lemma line (i : ℕ) (hi : i ≤ P.order) (h : P.Regular X f) {c} (e : P.supBounds o X f c)
    (A : Directions G n) (ht : ‖A‖ ≤ 1) :
    ‖Tensor.diagonal (iteratedFDeriv ℝ i (scaledFun P f) 0) A‖ ≤ c := by
  let y := P.threshold • A
  have he (t : ℝ) : P.threshold • (t • A)=t • y := smul_comm ..
  have hw : Tensor.diagonal (iteratedFDeriv ℝ i (scaledFun P f) 0) A = leftDerivs f (List.replicate i y) 1 := by
    rw [← iteratedDeriv_on_line (scaled_nice h i hi) A]
    unfold scaledFun; simp only [comp_apply,he]
    rw [← leftDerivs_diag, zero_smul, Work.G07.at_zero_increment]
  have hb : P.dirBound o y := by
    intro l; rw [show y l=P.threshold • A l from rfl,norm_smul,Real.norm_of_nonneg P.threshold_pos.le]
    exact mul_le_mul_of_nonneg_left (((norm_le_pi_norm _ _).trans ht).trans (one_le_pow₀ (by simp))) P.threshold_pos.le
  rw [hw]; apply e.2 1 (one_healthy _ _ P.threshold_pos.le)
  · rw [List.length_replicate]; exact hi
  intro A ha; rw [(List.mem_replicate.mp ha).2]; exact hb

private lemma mixed (G : Gauge) (i : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : Side) (X : Support n) (P : BudgetPoint)
    (o : Site n) (f : Config G n → ℂ) (p : ℝ), i ≤ P.order → P.Regular X f → P.supBounds o X f p →
    ∀ (v : Fin i → Directions G n), (∀ j, ‖v j‖ ≤ 1) → ‖iteratedFDeriv ℝ i (scaledFun P f) 0 v‖ ≤ c*p := by
  let m (x : Fin i → ℝ) := 1 + ∑ j, ‖x j‖
  have hm x : 0 < m x := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  obtain ⟨c,hc,J⟩ := diagonal_cost i (fun x => m x ^ i) (fun x => pow_nonneg (hm x).le _)
  refine ⟨c,hc,fun n X P o f p hi h e v hv => ?_⟩
  let F := iteratedFDeriv ℝ i (scaledFun P f) 0
  let T : (Fin i → ℝ) →L[ℝ] Directions G n := ∑ j : Fin i, (ContinuousLinearMap.proj (R:=ℝ) j).smulRight (v j)
  have he x : T x = ∑ j, x j • v j := by simp [T]
  let B := F.compContinuousLinearMap fun _ => T
  have hs : Tensor.Sym B := fun x s => Analysis.sym_Jet (scaled_nice h i hi) (T ∘ x) s
  have ht : B (fun j => Pi.single j 1) = F v := by
    unfold B; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    apply congr_arg F; funext j; simp [he,Pi.single_apply,ite_smul]
  rw [show iteratedFDeriv _ _ _ 0 v= _ from ht.symm]
  apply J B hs p e.1
  intro x
  let w := (m x)⁻¹ • (T x)
  have hu : ‖T x‖ ≤ m x := by
    rw [he]; apply (norm_sum_le ..).trans
    apply le_trans _ (le_add_of_nonneg_left zero_le_one)
    exact Finset.sum_le_sum fun j _ => by rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (hv j)
  have hx : ‖w‖ ≤ 1 := by
    rw [show w=_ from rfl, norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hm x)).le]
    exact (mul_le_mul_of_nonneg_left hu (by positivity)).trans_eq (inv_mul_cancel₀ (hm x).ne')
  have hz : T x = m x • w := by simp [w,smul_smul,(hm x).ne']
  change ‖Tensor.diagonal F (T x)‖ ≤ _
  rw [hz, Tensor.homogeneous, norm_smul,Real.norm_of_nonneg (pow_nonneg (hm x).le _)]
  exact mul_le_mul_of_nonneg_left (line i hi h e w hx) (pow_nonneg (hm x).le _)

def ticket (G : Gauge) (l : ℕ) : ℝ := (mixed G l).choose
lemma ticket_ok (G : Gauge) (i : ℕ) : 0 ≤ ticket G i := (mixed G i).choose_spec.1

lemma operator_cost (i : ℕ) (h : P.Regular X f) {p} (e : P.supBounds o X f p) (hi : i≤P.order) :
    ‖iteratedFDeriv ℝ i (scaledFun P f) 0‖ ≤ ticket G i * p := by
  let T := iteratedFDeriv ℝ i (scaledFun P f) 0
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (ticket_ok ..) e.1)
  intro v
  let m j := ‖v j‖
  let w : Fin i → Directions G n := fun j => (m j)⁻¹ • v j
  have ht j : ‖w j‖ ≤ 1 := by
    by_cases h : v j=0
    · simp [m,w,h]
    simp [w,m,h,norm_smul]
  have he : v=fun j => m j • w j := by
    funext j; by_cases h : v j=0 <;> simp [w,m,h,smul_smul]
  change ‖T v‖ ≤ _
  nth_rw 1 [he]; rw [T.map_smul_univ,norm_smul,Real.norm_of_nonneg]
  · rw [mul_comm (∏ j, m j)]
    exact mul_le_mul_of_nonneg_right ((mixed G i).choose_spec.2 n X P o f p hi h e w ht) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  exact Finset.prod_nonneg fun _ _ => norm_nonneg _

/-- Finite-order, local. -/
lemma composition_at_zero {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup W] [NormedSpace ℝ W] {f : H → W} {g : E → H}
    (l : ℕ) {A B : ℝ} (hf : ContDiffAt ℝ l f 0) (hg : ContDiffAt ℝ l g 0) (hz : g 0=0)
    (he : ∀ i : ℕ, i ≤ l → ‖iteratedFDeriv ℝ i f 0‖ ≤ A)
    (hu : ∀ i : ℕ, 1 ≤ i → i ≤ l → ‖iteratedFDeriv ℝ i g 0‖  ≤  B^i) :
    ‖Tensor.coeff (f ∘ g) l 0‖ ≤ A * B^l := by
  let F := Work.G05.blockTaylor l f
  let G := Work.G05.blockTaylor l g
  have hF : ContDiff ℝ (l:WithTop ℕ∞) F := Work.G05.blockTaylor_contDiff ..
  have hG : ContDiff ℝ (l:WithTop ℕ∞) G := Work.G05.blockTaylor_contDiff ..
  have hx : G 0=0 := (Work.G05.blockTaylor_zero ..).trans hz
  rw [Tensor.coeff,norm_smul,Real.norm_of_nonneg (show 0 ≤ (↑l.factorial:ℝ)⁻¹ by positivity)]
  rw [Work.G05.jets_comp hg hG.contDiffAt (by rwa [hz]) hF.contDiffAt (hz.trans hx.symm)
    (fun i hi => (Work.G05.blockTaylor_jets hg i hi).symm) (hx.symm ▸ fun i hi => (Work.G05.blockTaylor_jets hf i hi).symm) l le_rfl]
  have h := norm_iteratedFDeriv_comp_le hF hG le_rfl (0:E) (C:=A) (D:=B) (n:=l)
    (fun i hi => by unfold F; rw [hx, Work.G05.blockTaylor_jets hf i hi]; apply he i hi) (fun i hi hv => by
    unfold G; rw [Work.G05.blockTaylor_jets hg i hv]; exact hu i hi hv)
  exact (mul_le_mul_of_nonneg_left h (show 0 ≤ (↑l.factorial:ℝ)⁻¹ by positivity)).trans_eq (by field_simp)
end Costs
end YM.Further.CorrectedLift
