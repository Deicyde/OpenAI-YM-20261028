import YM.Pert.Lattice.Measure
/-! Real and complex formal polynomial integrands at a finite regulator. -/
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Orb
open MeasureTheory Function
variable {D E F : Type*} [NormedAddCommGroup D] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {R : Type*} [NormedRing R]

def Tame {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] (f : X → Y) := Continuous f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x, ‖f x‖ ≤ C * (1+‖x‖)^k
lemma Tame.constant (c : E) : Tame (fun _ : D => c) := ⟨continuous_const, ‖c‖, norm_nonneg _, 0, fun _ => (by simp)⟩
lemma Tame.clm (L : E →L[ℝ] F) : Tame (fun x : E => L x) := ⟨L.continuous, ‖L‖, norm_nonneg _, 1, fun x => by grw [L.le_opNorm]; simp; exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _) ⟩
lemma Tame.add {f g : D → E} (h : Tame f) (i : Tame g) : Tame (f+g) := by
  obtain ⟨C,hC,k,hf⟩ := h.2; obtain ⟨c,hc,l,hg⟩ := i.2
  refine ⟨h.1.add i.1,C+c,add_nonneg hC hc,max k l,fun x => ?_⟩
  grw [Pi.add_apply,norm_add_le,hf,hg,add_mul]
  gcongr <;> first | exact le_max_left .. | exact le_max_right .. | simp
lemma Tame.sum {I : Type*} {s : Finset I} {f : I → D → E} (h : ∀ i∈s, Tame (f i)) : Tame (∑ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact (Tame.constant (D:=D) (0:E))
  | insert a s he ih => rw [Finset.sum_insert he]; exact Tame.add (h _ (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
lemma Tame.mul {f g : D → R} (h : Tame f) (i : Tame g) : Tame (f*g) := by
  obtain ⟨C,hC,k,hf⟩ := h.2; obtain ⟨c,hc,l,hg⟩ := i.2
  refine ⟨h.1.mul i.1,C*c,mul_nonneg hC hc,k+l,fun x => ?_⟩
  grw [Pi.mul_apply,norm_mul_le _ _,hf,hg,pow_add]; ring_nf; exact le_rfl
lemma Tame.scalar_const {f : D → E} (h : Tame f) (c : ℝ) : Tame (c • f) := by
  obtain ⟨C,hC,k,hf⟩ := h.2
  refine ⟨h.1.const_smul c,‖c‖*C,by positivity,k,fun x => ?_⟩
  rw [Pi.smul_apply,norm_smul,mul_assoc]; gcongr; exact hf x
lemma Tame.scalar {g : D → ℝ} {f : D → E} (hg : Tame g) (h : Tame f) : Tame (g • f) := by
  obtain ⟨C,hC,k,hf⟩ := h.2; obtain ⟨c,hc,l,hg'⟩ := hg.2
  refine ⟨hg.1.smul h.1,c*C,mul_nonneg hc hC,l+k,fun x => ?_⟩
  change ‖g x • f x‖ ≤ _
  grw [norm_smul,hg',hf,pow_add]; ring_nf; exact le_rfl
lemma Tame.comp_clm {f : D → E} (h : Tame f) (L : E →L[ℝ] F) : Tame (fun x => L (f x)) := by
  obtain ⟨C,hC,k,hf⟩ := h.2
  refine ⟨L.continuous.comp h.1,‖L‖*C,by positivity,k,fun x => ?_⟩
  grw [L.le_opNorm,hf,mul_assoc]
lemma Tame.ofReal {f : D → ℝ} (h : Tame f) : Tame (fun x => (f x : ℂ)) := h.comp_clm Complex.ofRealCLM
lemma Tame.jet {k : ℕ} (L : E →L[ℝ] F) {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => F) Y) : Tame (fun x => T (fun _ => L x)) := by
  refine ⟨T.cont.comp (continuous_pi (fun _ => L.continuous)),‖T‖*‖L‖^k,by positivity,k,fun x => ?_⟩
  calc
    _ ≤ ‖T‖ * ∏ _ : Fin k, ‖L x‖ := T.le_opNorm _
    _ ≤ _ := by
      grw [L.le_opNorm, Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_assoc,← mul_pow]
      gcongr; linarith
lemma Tame.integrable {G : Gauge} {n : Lattice.Side} [CompleteSpace E] {f : Coords G n → E} (h : Tame f) : Integrable f (data G n) := by
  obtain ⟨C,_,k,hc⟩ := h.2
  exact ((moment_integrable k).const_mul C).mono' h.1.aestronglyMeasurable (Filter.Eventually.of_forall hc)
end YM.Pert.Orb

