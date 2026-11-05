import YM.RG08.Flat.Routing
import YM.UVExt.Consolidate

/-!
# Cover absolute sum adaptor

Real density/action coefficients. Rooted pushforwards preserve all
multiplicities in the coefficients (they need not in physical labels; not
being asserted here). Applied with pre-width weights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Push.AbsoluteSums Finset Function
open UVExt.Paths
open scoped Classical Topology ContDiff
variable {α β γ ι : Type*} {f g : α→ℝ} {k : β→ℝ} {A B : ℝ} {w w' : α → ℝ} {v : β → ℝ}

def Charge (w : α → ℝ) (f : α → ℝ) (A : ℝ) := SumBudget (fun i => w i*‖f i‖) A
namespace Charge
lemma mono (h : Charge w f A) (hp : ∀ i,0≤w' i) (hh : w' ≤ w) (ht : A ≤ B) : Charge w' f B :=
  budget_mono (budget_loosen h ht) (fun _ => mul_nonneg (hp _) (norm_nonneg _)) (fun _ => mul_le_mul_of_nonneg_right (hh _) (norm_nonneg _))
lemma nonneg (h : Charge w f A) : 0 ≤ A := budget_nonneg h
lemma summable (h : Charge w f A) (hh : ∀ i,1 ≤ w i) : Summable f := by
  have h : Charge (fun _=>1) f A := h.mono (fun _=> zero_le_one) hh le_rfl
  simpa only [one_mul,summable_norm_iff] using h.2.1
lemma scale (h : Charge w f A) (a : ℝ) : Charge w (a • f) (‖a‖*A) := by
  unfold Charge; simpa only [Pi.smul_apply,smul_eq_mul,norm_mul,mul_left_comm ‖a‖] using budget_scale (norm_nonneg a) h
lemma add (h : Charge w f A) (he : Charge w g B) (hp : ∀ i,0≤w i) : Charge w (f+g) (A+B) := by
  apply budget_mono (budget_plus h he) (fun i => mul_nonneg (hp i) (norm_nonneg _)) (fun i => ?_)
  simp only [Pi.add_apply]
  exact (mul_le_mul_of_nonneg_left (norm_add_le ..) (hp i)).trans_eq (mul_add ..)
lemma neg (h : Charge w f A) : Charge w (-f) A := by simpa using h.scale (-1)
lemma sub (h : Charge w f A) (he : Charge w g B) (hp : ∀ i,0≤w i) : Charge w (f-g) (A+B) := by
  rw [sub_eq_add_neg]; exact h.add he.neg hp
lemma swap (h : Charge w (f-g) A) : Charge w (g-f) A := by simpa using h.neg
lemma zero (w : α → ℝ) : Charge w 0 0 := by
  unfold Charge; simp only [Pi.zero_apply,norm_zero,mul_zero]; exact ⟨fun _=>le_rfl,summable_zero,tsum_zero.le⟩
lemma sums {s : Finset ι} {a : ι→ℝ} {F : ι→α→ℝ} (hp : ∀ i,0≤w i) (h : ∀ i∈s, Charge w (F i) (a i)) : Charge w (∑ i∈s,F i) (∑ i∈s,a i) := by
  induction s using Finset.induction_on with
  | empty => simpa using Charge.zero w
  | insert i s hi ih =>
    simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).add (ih fun j hj => h j (mem_insert_of_mem hj)) hp

lemma cross (h : Charge w f A) (he : Charge v k B) : Charge (fun i : α×β => w i.1*v i.2) (fun i => f i.1*k i.2) (A*B) := by
  unfold Charge; simpa only [norm_mul,mul_mul_mul_comm (w _) (v _)] using budget_prod h he

/-- Consumers generally have all target weights positive, not necessarily all
sites of target used. -/
lemma poolage (m : α → β) (hv : ∀ i,1≤v i) (h : Charge (fun i=> v (m i)) f A) : Charge v (pool f m) A := by
  let F (x) := ∑' i : {a // m a=x}, v (m i.val)*‖f i.val‖
  have hx : HasSum F (∑' i,v (m i)*‖f i‖) := h.2.1.hasSum.tsum_fiberwise m
  apply budget_mono (f:=F) ⟨fun _=>tsum_nonneg fun i=> h.1 i.val,hx.summable,hx.tsum_eq.trans_le h.2.2⟩ (fun _=>mul_nonneg ((hv _).trans' zero_le_one) (norm_nonneg _))
  intro i
  have he := (h.summable (fun i => hv _)).subtype (m · = i)
  apply le_trans (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm he.norm) ((hv _).trans' zero_le_one)) (le_of_eq ?_)
  rw [← tsum_mul_left]; exact tsum_congr fun x => by simp only [x.property]; rfl

end Charge

lemma pool_add (m : α→β) (hf : Summable f) (hg : Summable g) : pool (f+g) m=pool f m+pool g m :=
  funext fun i => (hf.subtype (m ·=i)).tsum_add (hg.subtype _)
lemma pool_scale (m : α→β) (a : ℝ) (f : α→ℝ) : pool (a • f) m=a • pool f m := funext fun _ => tsum_mul_left
lemma pool_minus (m : α→β) (hf : Summable f) (hg : Summable g) : pool (f-g) m=pool f m-pool g m :=
  funext fun i => (hf.subtype (m ·=i)).tsum_sub (hg.subtype _)
lemma pool_eq_zero (m : α→β) {z} (h : ∀ i,m i=z → f i=0) : pool f m z=0 := by
  unfold pool; exact (tsum_congr (g:=fun _=>0) fun i => h _ i.property).trans tsum_zero

-- Raw transfer before pooling onto new target.
def leads (f : α → ℝ) (k : α×β→ℝ) (i : α × β) : ℝ := f i.1*k i
lemma leads_cost {V : α×β→ℝ} {k : α×β→ℝ} (hb : 0≤B) (h : Charge w f A)
    (he : ∀ i, Charge (fun j => V (i,j)) (fun j => k (i,j)) (B*w i)) : Charge V (leads f k) (B*A) := by
  unfold Charge; apply budget_rows _ (fun i => B*(w i*‖f i‖)) _ (budget_scale hb h)
  intro i; have hh := (he i).scale (f i)
  rw [show B*(w i*‖f i‖)=‖f i‖*(B*w i) by ring]; exact hh
lemma leads_add (a b : α→ℝ) (k : α×β→ℝ) : leads (a+b) k=leads a k+leads b k := funext fun _ => add_mul ..
lemma leads_scale (a : ℝ) (f : α→ℝ) (k : α×β→ℝ) : leads (a • f) k=a • leads f k := funext fun _ => mul_assoc ..
lemma leads_minus (a b : α→ℝ) (k : α×β→ℝ) : leads (a-b) k=leads a k-leads b k := funext fun _ => sub_mul ..
lemma leads_diff (a : α→ℝ) (k m : α×β→ℝ) : leads a (k-m)=leads a k-leads a m := funext fun _ => mul_sub ..

lemma sum_bounded (hf : Summable f) (hh : ∀ i, ‖g i‖ ≤ B) : Summable (fun i => f i*g i) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i => ?_) (hf.norm.mul_right B)
  rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hh _) (norm_nonneg _)
lemma pool_total (v : β → ℝ) (m : α→β) (hf : Summable f) (hv : ∀ i, ‖v i‖ ≤ B) :
    ∑' i, pool f m i * v i=∑' i, f i*v (m i) :=
  (pool_read f v m hf (sum_bounded hf (fun _ => hv _))).tsum_eq
end YM.RG08
