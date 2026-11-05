import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Currency
import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Voyage
import YM.Next.FREE_KERNELS.Lifts

/-!
# Patch frames. Pricing a family, l² after average over patch arguments

Important that at most one rough leg is needed. At the `Spend` layer (when such
a leg is present) uniform average of absolute sizes over β, *then* unnormalized
l² over α. Needn't establish sup over all fine patch arguments in this case.
Watch for frame patch paths: when the mark comes from one leg of a path
product, need actual estimates paying such a bill out of the available
l² on that leg (see `Visit` using bounded multiplicities).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch
open Progress.StationaryScenes Work.F03 YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

namespace Purse
variable {X Y Z ι α β γ : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    [Fintype α] [Fintype β] [Nonempty β] [Fintype γ] [Nonempty γ]

lemma avg_pos (x : β→ℝ) (h : ∀ i, 0 ≤ x i) : 0 ≤ avg x := (avg_const (n:=β) (0:ℝ)).ge.trans (avg_mono (fun i => h i))

def Spend (P : Purse ι α) (S : Finset ι) (f : α→β→X) (C : ℝ) := 0 ≤ C ∧
    (¬ P.tagged S → ∀ i j, P.price S i * ‖f i j‖ ≤ C*P.target S) ∧
    (P.tagged S → rlen (fun i => avg fun j => P.price S i * ‖f i j‖) ≤ P.cap*C*P.target S)
variable {P : Purse ι α} {f : α→β→X} {g : α→β→Y} {u : α→β→Z} {S T : Finset ι} {C D : ℝ}
omit [Fintype α] in
lemma house (P : Purse ι α) (S : Finset ι) (f : α→β→X) (i) : 0 ≤ avg fun j => P.price S i*‖f i j‖ := avg_pos _ fun _ => mul_nonneg (P.price_pos _ _).le (norm_nonneg _)
omit [Nonempty β] in
lemma Spend.mono (h : P.Spend S f C) (hc : C ≤ D) : P.Spend S f D := ⟨h.1.trans hc,fun ht i j =>
    (h.2.1 ht i j).trans (mul_le_mul_of_nonneg_right hc (P.target_pos _)),fun ht => (h.2.2 ht).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc P.rooted) (P.target_pos _))⟩
lemma Spend.change (h : P.Spend S f C) (hv : ∀ i j, ‖g i j‖ ≤ ‖f i j‖) : P.Spend S g C := by
  have he (i) (j) := mul_le_mul_of_nonneg_left (hv i j) (P.price_pos S i).le
  exact ⟨h.1,fun ht i j => (he ..).trans (h.2.1 ht i j),fun ht =>
    (rless (house P S g) (fun i => avg_mono (he i))).trans (h.2.2 ht)⟩
lemma Spend.zero {D : ℝ} (hx : 0 ≤ D) : P.Spend S (fun _ => fun _ : β => (0:X)) D := by
  unfold Spend
  simp only [norm_zero,mul_zero, avg_const]
  exact ⟨hx,fun _ _ _ => mul_nonneg hx (P.target_pos _),fun _ => (ell_zero.le).trans
    (mul_nonneg (mul_nonneg P.rooted hx) (P.target_pos _))⟩
omit [Nonempty β] in
lemma Spend.blank (h : 0 ≤ C) (he : ∀ i j, ‖f i j‖ ≤ C) : P.Spend ∅ f C := by
  refine ⟨h,fun _ i j => ?_,fun ⟨_,hx,_⟩ => ?_⟩
  · simpa [price,target] using he i j
  simp at hx
lemma Spend.sending (h : P.Spend S f C) (ht : 0 ≤ D) (l : Equiv.Perm α) (he : ∀ i j,P.price S i * ‖g i j‖ ≤ D*(P.price S (l i)*‖f (l i) j‖)) : P.Spend S g (D*C) := by
  refine ⟨mul_nonneg ht h.1,fun hx i j => (he i j).trans ((mul_le_mul_of_nonneg_left (h.2.1 hx _ j) ht).trans_eq (mul_assoc ..).symm),fun hx => ?_⟩
  let b (i : α) := avg fun j => P.price S i*‖f i j‖
  have hh i : avg (fun j => P.price S i*‖g i j‖) ≤ D*((b ∘ l) i) := (avg_mono (he i)).trans_eq (avg_mul _ _)
  apply (rless (house P S g) hh).trans
  rw [rconstant ht (b ∘ l),rperm]; exact (mul_le_mul_of_nonneg_left (h.2.2 hx) ht).trans_eq (by ring)
lemma Spend.rate (h : P.Spend S f C) (ht : 0 ≤ D) (he : ∀ i j, ‖g i j‖ ≤ D*‖f i j‖) : P.Spend S g (D*C) :=
    h.sending ht (Equiv.refl α) fun i j => ((mul_le_mul_of_nonneg_left (he i j) (P.price_pos _ _).le).trans_eq (mul_left_comm ..))
lemma Spend.plus {e : α→β→X} (h : P.Spend S f C) (ht : P.Spend S e D) : P.Spend S (f+e) (C+D) := by
  have ha i j : P.price S i * ‖(f+e) i j‖ ≤ P.price S i*‖f i j‖ + P.price S i*‖e i j‖ := (mul_le_mul_of_nonneg_left
    (norm_add_le ..) (P.price_pos _ _).le).trans_eq (mul_add ..)
  refine ⟨add_nonneg h.1 ht.1,fun he i j => (ha ..).trans ((add_le_add (h.2.1 he i j) (ht.2.1 he i j)).trans_eq (add_mul ..).symm),fun he => ?_⟩
  exact (rtriangle (house P S (f+e)) (fun i => (avg_mono (ha i)).trans_eq (avg_add ..))).trans
    ((add_le_add (h.2.2 he) (ht.2.2 he)).trans_eq (by ring))
lemma Spend.finite {κ : Type*} {g : κ→α→β→X} {B : κ→ℝ} (q : Finset κ) (h : ∀ i ∈ q,P.Spend S (g i) (B i)) :
    P.Spend S (∑ i∈q,g i) (∑ i∈q, B i) := by
  classical
  induction q using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact (Spend.zero le_rfl (P:=P) (β:=β) (S:=S) (D:=0) (X:=X))
  | insert i q hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h _ (by simp)).plus (ih (fun j hj => h _ (Finset.mem_insert_of_mem hj)))

omit [Nonempty β] in
lemma Spend.heavy [NormedSpace ℝ X] (h : P.Spend S f C) (w : β→ℝ) (he : ∑ i,w i=1) (hw : ∀ i, 0 ≤ w i)
    (hb : 1 ≤ D) (ht : ∀ i, w i ≤ D/(Fintype.card β:ℝ)) : P.Pays S (fun i => ∑ j,w j • f i j) (D*C) := by
  have ha i : P.price S i * ‖∑ j,w j • f i j‖ ≤ ∑ j, w j*(P.price S i*‖f i j‖) := by
    apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (P.price_pos _ _).le).trans_eq
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; rw [norm_smul,Real.norm_of_nonneg (hw j),mul_left_comm]
  have hd := zero_le_one.trans hb
  refine ⟨mul_nonneg hd h.1,fun hi i => (ha i).trans ?_,fun hi => ?_⟩
  · apply ((Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h.2.1 hi i j) (hw j))).trans _)
    rw [← Finset.sum_mul, he,one_mul]; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left h.1 hb) (P.target_pos _)
  have hk i := (ha i).trans (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (ht j)
    (mul_nonneg (P.price_pos S i).le (norm_nonneg (f i j)))))
  let b i := avg fun j => P.price S i*‖f i j‖
  apply (rless (fun i => mul_nonneg (P.price_pos _ _).le (norm_nonneg _)) (fun i => (hk i).trans_eq (show _=D*b i from by rw [← Finset.mul_sum]; unfold b avg; rw [smul_eq_mul]; ring))).trans
  rw [rconstant hd b]; exact (mul_le_mul_of_nonneg_left (h.2.2 hi) hd).trans_eq (by ring)
lemma energize {z : α→X} (h : P.Pays S z C) : P.Spend S (fun i => fun _ : β => z i) C := ⟨h.1,fun he i _ => h.2.1 he i,fun he => by simp only [avg_const]; exact h.2.2 he⟩
lemma alonePay {z : α→X} (h : P.Spend S (fun i => fun _ : Unit => z i) C) : P.Pays S z C := ⟨h.1,fun he i => h.2.1 he i (),fun he => by
  have hh := h.2.2 he; simpa only [avg_const] using hh⟩
omit [Nonempty β] [Nonempty γ] in
lemma poolAverage (f : β×γ → ℝ) : avg f = avg fun i : β => avg fun j : γ => f (i,j) := by
  unfold avg; simp only [smul_eq_mul, Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type]; rw [← Finset.mul_sum]; simp [mul_comm]; ring
lemma Spend.pooled [NormedSpace ℝ X] {g : α → β×γ → X} (h : P.Spend S g C) :
    P.Spend S (fun i j => avg fun k => g i (j,k)) C := by
  have ht i j : P.price S i*‖avg fun k => g i (j,k)‖ ≤ avg fun k => P.price S i * ‖g i (j,k)‖ := by rw [avg_mul]; exact mul_le_mul_of_nonneg_left (norm_avg _) (P.price_pos _ _).le
  exact ⟨h.1,fun he i j => (ht i j).trans ((avg_mono (fun k => h.2.1 he i (j,k))).trans_eq (avg_const _)),fun he =>
    (rless (house P S _) (fun i => (avg_mono (ht i)).trans_eq (poolAverage (fun j => P.price S i*‖g i j‖)).symm)).trans (h.2.2 he)⟩
omit [Nonempty β] in
lemma Spend.reuses (h : P.Spend S f C) : P.Spend S (fun i p => f i (p : β × γ).1) C := ⟨h.1,fun he i p => h.2.1 he i p.1,fun he => by simp_rw [poolAverage,avg_const]; exact h.2.2 he⟩
omit [Nonempty β] [Nonempty γ] in
lemma Spend.reshapes (e : γ ≃ β) (h : P.Spend S f C) : P.Spend S (fun i p => f i (e p)) C := ⟨h.1,fun he i p => h.2.1 he i _,fun he => by
  convert! h.2.2 he using 2; congr! 1 with i
  unfold avg; rw [Fintype.card_congr e]; rw [Equiv.sum_comp e (fun p => P.price S i * ‖f i p‖)]⟩

omit [Fintype α] in
lemma both {S T : Finset ι} (h : Disjoint S T) (u : P.tagged S) : ¬ P.tagged T := by
  obtain ⟨i,hi,he⟩ := u; rintro ⟨j,hj,hv⟩; rw [Option.some.inj (he.symm.trans hv)] at hi; exact Finset.disjoint_left.mp h hi hj
variable [DecidableEq ι]
omit [Fintype α] in
lemma together {S T : Finset ι} : P.tagged (S∪T) ↔ P.tagged S ∨ P.tagged T := by simp only [tagged, Finset.mem_union]; grind
lemma Spend.times (h : P.Spend S f C) (hp : P.Spend T g D) (ht : Disjoint S T) (hu : ∀ i j, ‖u i j‖ ≤ ‖f i j‖*‖g i j‖) : P.Spend (S∪T) u (C*D) := by
  have ha (i) (j) : P.price (S∪T) i*‖u i j‖ ≤ (P.price S i*‖f i j‖)*(P.price T i*‖g i j‖) := by
    apply (mul_le_mul_of_nonneg_left (hu i j) (P.price_pos _ _).le).trans_eq; unfold price; rw [Finset.prod_union ht]; ring
  unfold Spend
  rw [show P.target (S∪T)=P.target S*P.target T from Finset.prod_union ht,together]
  refine ⟨mul_nonneg h.1 hp.1,fun e i j => ?_,fun e => ?_⟩
  · exact (ha i j).trans ((mul_le_mul (h.2.1 (fun x => e (Or.inl x)) i j) (hp.2.1 (fun x => e (Or.inr x)) i j)
      (mul_nonneg (P.price_pos ..).le (norm_nonneg _)) (mul_nonneg h.1 (P.target_pos _))).trans_eq (by ring))
  rcases e with H|H
  · let b i := avg fun j => P.price S i*‖f i j‖
    have hD := mul_nonneg hp.1 (P.target_pos T)
    have hh (i) : avg (fun j => P.price (S∪T) i*‖u i j‖) ≤ D*P.target T*b i := (avg_mono
      (fun j => (ha i j).trans ((mul_le_mul_of_nonneg_left (hp.2.1 (both ht H) i j)
        (mul_nonneg (P.price_pos _ _).le (norm_nonneg _))).trans_eq (mul_comm ..)))).trans_eq (avg_mul ..)
    apply (rless (house P (S∪T) u) hh).trans
    rw [rconstant hD b]; exact (mul_le_mul_of_nonneg_left (h.2.2 H) hD).trans_eq (by ring)
  let b i := avg fun j => P.price T i*‖g i j‖
  have hC := mul_nonneg h.1 (P.target_pos S)
  have hh i := (avg_mono (fun j => (ha i j).trans (mul_le_mul_of_nonneg_right (h.2.1 (both ht.symm H) i j)
    (mul_nonneg (P.price_pos _ _).le (norm_nonneg _))))).trans_eq (show _=C*P.target S*b i from avg_mul ..)
  apply (rless (house P (S∪T) u) hh).trans
  rw [rconstant hC b]; exact (mul_le_mul_of_nonneg_left (hp.2.2 H) hC).trans_eq (by ring)
end Purse
end YM.AnalyticNext.QuarticMatch.Estimate
