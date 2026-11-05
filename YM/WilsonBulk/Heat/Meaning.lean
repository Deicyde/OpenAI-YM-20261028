import YM.WilsonBulk.Heat.Scape
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite polynomial meaning of the kernel operations

Exact ordinary symmetric coefficients, *not* amputated amplitudes nor
jet-array norms. Color basis already elementary slot labels. All equations
at finite index set (independent of number of sites).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Classical Topology BigOperators
open Function Equiv Finset
open MvPolynomial (pderiv C X)
variable {α : Type} {k n r : ℕ} {G : Page α 2}
abbrev Formula (α : Type) := MvPolynomial α ℝ

def field (v : Legs α n) : Formula α := ∏ i,X (v i)
def margin (u : Page α (n+1)) (x : α) : Page α n := fun v=> u (hitch x v)
lemma Regular.margin {P : Page α (n+1)} (h : Regular P) (x : α) : Regular (margin P x) := by
  intro e; ext1 a; let E : Perm (Fin (n+1)):= (finSuccEquiv n).trans ((optionCongr e).trans (finSuccEquiv n).symm)
  refine Eq.trans (congr_arg P ?_) (h.eq E (hitch x a)); ext1 i; cases i using Fin.cases <;> simp [E]
lemma Regular.twice {P : Page α (n+2)} (h : Regular P) (x y : α) : Sheet.margin (Sheet.margin P x) y = Sheet.margin (Sheet.margin P y) x := by
  ext1 a; let i : Fin (n+2):= (0:Fin (n+1)).succ; let e : Perm (Fin (n+2)):= swap 0 i
  refine Eq.trans (congr_arg P ?_) (h.eq e (hitch y (hitch x a))); ext1 j
  cases j using Fin.cases
  · simp only [comp_apply,i,e, swap_apply_left, hitch_zero,hitch_succ]
  rename_i j; cases j using Fin.cases
  · simp only [comp_apply,i,e,swap_apply_right, hitch_succ,hitch_zero]
  · rename_i j; rw [comp_apply,swap_apply_of_ne_of_ne]; simp
    · simp
    exact fun he=> Fin.succ_ne_zero j (Fin.succ_inj.mp he)
lemma typeset_fin_hitch {β : Type} [Fintype α] [AddCommMonoid β] (f : Legs α (n+1) → β) :
    ∑ i,f i = ∑ x:α,∑ v : Legs α n, f (hitch x v) := by
  rw [← Equiv.sum_comp (hitchEquiv α n) f,Fintype.sum_prod_type]; rfl
lemma typeset_fin_plus {β : Type} [Fintype α] [AddCommMonoid β] (f : Legs α (k+n) → β) :
    ∑ i,f i = ∑ v : Legs α k,∑ w : Legs α n, f (Fin.append v w) := by
  rw [← Equiv.sum_comp (halves α k n) f,Fintype.sum_prod_type]; rfl
lemma field_cast (v : Legs α n) (e : Fin k≃ Fin n) : field (v ∘ e)=field v := Equiv.prod_comp e (fun i=> X (R:=ℝ) (v i))
lemma field_hitch (x : α) (v : Legs α n) : field (hitch x v)= X x * field v := by simp only [field,hitch_zero,hitch_succ,Fin.prod_univ_succ]
lemma field_append (v : Legs α n) (w : Legs α k) : field (Fin.append v w)=field v*field w := by simp only [field,Fin.prod_univ_add,Fin.append_left,Fin.append_right]

variable [Fintype α]

def script (P : Page α n) : Formula α := ∑ a,C (P a) * field a
@[simp] lemma script_zero : script (0:Page α n)=0 := by simp [script]
lemma script_scale (P : Page α n) (r : ℝ) : script (r • P)= r • script P := by
  unfold script; simp only [Pi.smul_apply,smul_eq_mul,map_mul,mul_assoc,← mul_sum]; exact MvPolynomial.C_mul'
lemma script_plus (u v : Page α n) : script (u+v) = script u + script v := by simp only [script,Pi.add_apply,map_add, add_mul,Finset.sum_add_distrib]
lemma script_minus (u v : Page α n) : script (u-v)= script u-script v := by simp only [script,Pi.sub_apply,map_sub, sub_mul,sum_sub_distrib]
lemma script_sum {ι : Type} (s : Finset ι) (p : ι → Page α n) : script (∑ i∈s,p i)=∑ i∈s,script (p i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s h ih => simp only [sum_insert h, script_plus, ih]
lemma script_escort (e : Fin k≃ Fin n) (u : Page α k) : script (escort e u) = script u := by
  unfold script; rw [← Equiv.sum_comp (casesEquiv e.symm (Equiv.refl _)) (fun i=> C (u i) * field i)]
  refine sum_congr rfl fun a _=>?_ ; rw [show casesEquiv e.symm _ a=a ∘ (e:Fin k→Fin n) from by rw [casesEquiv_apply]; rfl,field_cast]; rfl
lemma script_polish (u : Page α n) : script (polish u) = script u := by
  simp only [polish,script_scale, script_sum,script_escort,sum_const,card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ]; exact inv_smul_smul₀ (by positivity) _
lemma script_trace (u : Page α (n+1)) : script u = ∑ x : α,X x * script (margin u x) := by
  simp only [script,margin,mul_sum,typeset_fin_hitch (fun a:Legs α (n+1)=> C _ * field a),field_hitch]; refine sum_congr rfl fun x _=>sum_congr rfl fun _ _=> ?_; ring
lemma script_scalar (u : Page α 0) : script u = C (u Fin.elim0) := by simp [script,field,Unique.eq_default (show Legs α 0 from Fin.elim0)]
lemma script_scalar_injective : Injective (fun u : Page α 0=>script u) := by
  intro u v h; dsimp only at h; rw [script_scalar, script_scalar] at h; exact funext fun i => Subsingleton.elim (show Legs α 0 from Fin.elim0) i ▸ MvPolynomial.C_injective (R:=ℝ) α h
lemma script_dual (P : Page α n) (x : α → ℝ) : MvPolynomial.eval x (script P)=∑ i,P i * ∏ j,x (i j) := by
  simp only [script,map_sum,map_mul,field,map_prod,MvPolynomial.eval_X,MvPolynomial.eval_C]

-- derivative identity and injectivity on Regular coefficients (later used to pass Ward)
lemma script_deriv (u : Page α (n+1)) (h : Regular u) (x : α) :
    pderiv x (script u) = ((n+1:ℕ):ℝ) • script (margin u x) := by
  induction n with
  | zero =>
    rw [script_trace,map_sum]; simp_rw [script_scalar, MvPolynomial.pderiv_mul]
    simp [Pi.single_apply]
  | succ n ih=>
    rw [script_trace,map_sum]; simp_rw [MvPolynomial.pderiv_mul,ih _ (h.margin _),h.twice _ x,Finset.sum_add_distrib]
    -- normalize powers
    rw [show (∑ i:α, pderiv x (X (R:=ℝ) i)*script (margin u i))=script (margin u x) from by simp [Pi.single_apply,ite_mul]]
    conv_rhs => rw [script_trace]
    conv_lhs => arg 1; rw [script_trace]
    push_cast
    rw [add_smul, one_smul]; simp_rw [mul_smul_comm,← Finset.smul_sum,add_comm _ ((_ : ℝ) • _)]

lemma script_trust {u v : Page α n} (hu : Regular u) (hv : Regular v) (h : script u=script v) : u=v := by
  induction n with
  | zero => exact script_scalar_injective h
  | succ n ih =>
    ext1 a; refine legs_succ (fun a:Legs α (n+1)=> u a = v a) (fun x v'=>?_) a
    apply congr_fun (f:=margin u x) (ih (hu.margin x) (hv.margin x) ?_) v'
    exact smul_right_injective _ (show ((n+1:ℕ):ℝ)≠0 by positivity) ((script_deriv u hu x).symm.trans ((congrArg (fun w:Formula α=>pderiv x w) h).trans (script_deriv _ hv x)))

end YM.WilsonBulk.Sheet
