import YM.RG08.Ballast.Tune
import YM.RG08.Ballast.Grapes

/-!
# Assembly of Banach-valued rooted packets for the formal measure lanes

Use exponential, also polynomial at cut/capture. No raw-activity identity.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Quire
open RG Laurent Lattice Wilson Bloch Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary
open scoped Topology ContDiff Classical BigOperators
variable {α β γ ι E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {A B C w σ : ℝ} {r : ℕ}

def Ink (v : α →ℝ) (f : α→E) (A : ℝ) := SumBudget (fun i=> v i*‖f i‖) A
variable {v v' : α→ℝ} {u : β→ℝ} {p q : α→E}
def Pens (f : α→E) := Summable fun i=>‖f i‖
lemma pens_for {f : α→ℝ} : Pens f↔Summable f := summable_norm_iff
variable (α E) in
lemma Pens.zero : Pens (0:α→E) := by unfold Pens; simp
lemma Pens.plus (h : Pens p) (g : Pens q) : Pens (p+q) := Summable.of_nonneg_of_le (fun i=>norm_nonneg _)
    (fun i=>norm_add_le ..) (h.add g)
lemma Pens.neg (h : Pens p) : Pens (-p) := by simpa [Pens] using h
lemma Pens.less (h : Pens p) (g : Pens q) : Pens (p-q) := sub_eq_add_neg p q ▸ h.plus g.neg
lemma Pens.additions {s : Finset ι} {f : ι→α→E} (h : ∀ i∈s, Pens (f i)) : Pens (∑ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty=>rw [sum_empty]; exact Pens.zero ..
  | insert j s hj ih=> rw [sum_insert hj]; exact (h _ (mem_insert_self ..)).plus (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma Ink.none (v : α→ℝ) (E : Type*) [NormedAddCommGroup E] : Ink v (0:α→E) 0 := by unfold Ink; simp only [Pi.zero_apply,norm_zero,mul_zero]; exact ⟨fun _=>le_rfl,summable_zero,tsum_zero.le⟩
lemma Ink.raise (h : Ink v p A) (he : A≤B) : Ink v p B := budget_loosen h he
lemma Ink.shrink (h : Ink v p A) (hv : 0≤v') (hp : v'≤v) : Ink v' p A := budget_mono h (fun i=>mul_nonneg (hv i) (norm_nonneg _)) (fun i=>mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _))
lemma Ink.nonneg (h : Ink v p A) : 0≤A := budget_nonneg h
lemma Ink.plus (h : Ink v p A) (g : Ink v q B) (hv : 0≤v) : Ink v (p+q) (A+B) := budget_mono (budget_plus h g)
    (fun i=> mul_nonneg (hv i) (norm_nonneg _)) (fun i=> (mul_le_mul_of_nonneg_left (norm_add_le ..) (hv i)).trans_eq (mul_add ..))
lemma Ink.neg (h : Ink v p A) : Ink v (-p) A := by simpa [Ink] using h
lemma Ink.less (h : Ink v p A) (g : Ink v q B) (hp : 0≤v) : Ink v (p-q) (A+B) := sub_eq_add_neg p q ▸ h.plus g.neg hp
lemma Ink.additions {s : Finset ι} {f : ι→α→E} {g : ι→ℝ} (he :∀ i∈s, Ink v (f i) (g i)) (hv : 0≤v) : Ink v (∑ i∈s,f i) (∑ i∈s,g i) := by
  induction s using Finset.induction_on with
  | empty => rw [sum_empty,sum_empty]; exact Ink.none ..
  | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact (he _ (mem_insert_self ..)).plus (ih fun j hj=> he j (mem_insert_of_mem hj)) hv
lemma Ink.pens (h : Ink v p A) (hx : 1≤v) : Pens p := by
  simpa only [Pens, Ink, Pi.one_apply,one_mul] using (h.shrink (fun _=>zero_le_one) hx).2.1
lemma Pens.priced (h : Pens p) : Ink 1 p (∑' i, ‖p i‖) := by
  unfold Ink; simp only [Pi.one_apply,one_mul]; exact ⟨fun i=>norm_nonneg _,h,le_rfl⟩

section Real
variable [NormedSpace ℝ E] [NormedSpace ℝ F]
lemma Ink.scale (h : Ink v p A) (c : ℝ) : Ink v (c • p) (‖c‖*A) := by
  unfold Ink; simpa only [Pi.smul_apply, norm_smul, mul_left_comm ‖c‖] using budget_scale (norm_nonneg c) h
lemma Ink.some (h : Ink v p A) (e : E→L[ℝ] F) (hp : 0≤v) : Ink v (e ∘ p) (‖e‖*A) := budget_mono (budget_scale (norm_nonneg e) h)
  (fun i=>mul_nonneg (hp i) (norm_nonneg _)) (fun i=> (mul_le_mul_of_nonneg_left (e.le_opNorm _) (hp i)).trans_eq (mul_left_comm ..))
lemma Ink.prods (h : Ink v p A) {f : β→ℝ} (e : Charge u f C) : Ink (fun x : α×β=> v x.1*u x.2)
    (fun x=>f x.2 • p x.1) (A*C) := by
  unfold Ink; simp_rw [norm_smul,mul_comm ‖f _‖,mul_mul_mul_comm (v _) (u _)]; exact budget_prod h e

def sires (p : α → E) (k : α × β→ℝ) (x : α×β) := k x • p x.1
lemma Ink.sires_cost (h : Ink v p A) (hv : α×β→ℝ) (k : α×β→ℝ) (hb : 0≤B)
    (hk : ∀ i, Charge (fun j=>hv (i,j)) (fun j=>k (i,j)) (B*v i)) : Ink hv (sires p k) (B*A) := by
  unfold Ink; apply budget_rows _ (fun i=> B*(v i*‖p i‖)) _ (budget_scale hb h); intro i
  unfold sires; simp_rw [norm_smul]; rw [show B*(v i*‖p i‖)=‖p i‖*(B*v i) from by ring]; convert budget_scale (norm_nonneg (p i)) (hk i) using 1; ext j; ring

lemma Pens.shaped (h : Pens p) (A : E→L[ℝ] F) : Pens (A ∘ p) := (h.priced.some A (fun _=>zero_le_one)).pens le_rfl
lemma Pens.scale (h : Pens p) (c : ℝ) : Pens (c • p) := (h.priced.scale c).pens le_rfl
end Real

def tub (p : α→E) (m : α→β) (z : β) := ∑' i : {a // m a=z}, p i.val
section tub
variable [CompleteSpace E] (m : α→β)
lemma Ink.pour (h : Ink (u ∘ m) p A) (hv : 1≤u) : Ink u (tub p m) A := by
  have hx := h.pens (fun i=>hv _)
  have he := h.2.1.hasSum.tsum_fiberwise m
  apply budget_mono ⟨fun i=> tsum_nonneg fun t=>h.1 _,he.summable, he.tsum_eq.trans_le h.2.2⟩ (fun i=>mul_nonneg ((hv i).trans' zero_le_one) (norm_nonneg _))
  intro i; apply le_trans (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (Summable.subtype hx (m · = i))) ((hv i).trans' zero_le_one)) (le_of_eq ?_); rw [← tsum_mul_left]; exact tsum_congr fun x : {j // m j=i}=> by simp [x.property]
lemma Pens.pours (h : Pens p) : Pens (tub p m) := Ink.pens (Ink.pour (u:=1) m h.priced (show (1:β→ℝ)≤ 1 from le_rfl)) le_rfl
lemma Pens.tub_plus (h : Pens p) (g : Pens q) : tub (p+q) m=tub p m + tub q m := funext fun i=> (Summable.of_norm (Summable.subtype h (m · = i))).tsum_add (Summable.of_norm (Summable.subtype g (m ·=i)))
lemma Pens.tub_sub (h : Pens p) (g : Pens q) : tub (p-q) m=tub p m-tub q m := funext fun i=> (Summable.of_norm (Summable.subtype h (m · = i))).tsum_sub (Summable.of_norm (Summable.subtype g (m ·=i)))
lemma Pens.echo_pool [NormedSpace ℝ E] [NormedSpace ℝ F] (h : Pens p) (e : E→L[ℝ] F) : e ∘ tub p m=tub (e ∘ p) m := funext fun i=> by
  unfold tub; exact e.map_tsum (Summable.of_norm (Summable.subtype h (m · = i)))
end tub
end YM.RG08.Quire
