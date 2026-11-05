import YM.WilsonBulk.Transit.Scores
import YM.WilsonBulk.Staves.Encounter

/-!
# Polynomial budgets and tests (coordinate all other slots), general planted
 letter assembly. Use `Weight` for translation coordinates of root-relative
 costs in actual Laurent moment. Penetrate are rank-positive, never asserts
 support coherence across period unless pushed separately. Color generic.
 Includes generation by ALL lists with possible collision among repeated legs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet.Taylor
open Push.AbsoluteSums Function Filter Finset Lattice Laurent RG Pert.Bulk
open scoped Topology BigOperators Classical ENNReal
open MvPolynomial (X C rename eval)
variable {α β γ : Type} {σ τ p q : ℝ} {f g : Formula α} {n d : ℕ}

def league : List α→ Formula α := fun a=> (a.map MvPolynomial.X).prod
@[simp] lemma league_empty : league ([]:List α)=1 := rfl
@[simp] lemma league_p (x : α) (a : List α) : league (x::a)=X x*league a:=rfl
lemma league_padded (x : List α) (p : α) (d : ℕ) : league (x ++ List.replicate d p)= league x * X p ^ d := by simp [league]
lemma league_append (x y : List α) : league (x++y)=league x* league y := by simp [league]
lemma league_grade (L : List α) : (league L).totalDegree ≤ L.length := by
  induction L with
  | nil=> simp
  | cons i l h=> rw [league_p]; exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_X,List.length_cons]; omega)
-- decompose monomial by repeated indices
def load (d : α →₀ ℕ) := d.sum fun _ u=>u
lemma load_total (d e : α →₀ ℕ) : load (d+e)=load d+load e:= by unfold load; rw [Finsupp.sum_add_index'] <;> intros <;> rfl
lemma league_bill (d : α →₀ ℕ) : ∃ L : List α,L.length=load d ∧ league L=MvPolynomial.monomial d (1:ℝ) := by
  induction d using Finsupp.induction_linear with
  | zero=> exact ⟨[],by simp [load],rfl⟩
  | add x y hx hy=>
    obtain ⟨L,hL,h⟩:= hx; obtain ⟨K,hK,k⟩:= hy; exact ⟨L++K,by rw [List.length_append,hL,hK,load_total],by simp [league_append,h,k,MvPolynomial.monomial_mul]⟩
  | single x i=> exact ⟨List.replicate i x,by simp [load],by simp [league,MvPolynomial.X_pow_eq_monomial]⟩

lemma list_suffices [AddCommGroup β] [Module ℝ β] (w : Formula α→ₗ[ℝ]β) (p : Formula α) {n : ℕ} (h : ∀ l : List α,l.length<n → w (league l)=0) (ht : p.totalDegree < n) : w p=0 := by
  nth_rw 1 [← MvPolynomial.support_sum_monomial_coeff p]; rw [map_sum]; refine sum_eq_zero fun i hi=>?_ ; obtain ⟨l,hl,hP⟩:= league_bill i
  rw [show MvPolynomial.monomial i (MvPolynomial.coeff i p)=(MvPolynomial.coeff i p) • league l from ?_,map_smul,h l (by rw [hl]; exact (MvPolynomial.le_totalDegree hi).trans_lt ht),smul_zero]; rw [hP]; simp [MvPolynomial.smul_monomial]

variable [Fintype α]
lemma amount_on (i : α) (x : Move α) : ‖((x i):ℝ)‖ ≤ size x := by
  have hu : ‖((x i):ℝ)‖=((x i).natAbs:ℝ):= by norm_num
  rw [hu]; exact_mod_cast (show (x i).natAbs ≤ _ from Finset.single_le_sum (f:=fun i=> (x i).natAbs) (fun i _=> Nat.zero_le _) (mem_univ i))
-- polynomial growth & absolute cost
lemma league_limit (l : List α) (v : Move α) : ‖lineRead v (league l)‖≤ (1+(size v:ℝ))^l.length := by
  induction l with
  | nil=>simp [lineRead]
  | cons x l ih=> simp only [league_p,List.length_cons,lineRead,map_mul,norm_mul, MvPolynomial.eval_X, pow_succ']; exact mul_le_mul ((amount_on x v).trans (by linarith)) ih (norm_nonneg _) (by positivity)
lemma meters_league (l : List α) (hs : 0< σ) {u : Move α→ℝ} (h : Width σ p u) : SumBudget (fun x : Move α=>‖u x*lineRead x (league l)‖) (momentWeight σ l.length*p) := by
  refine Work.F08.budget_minor (Push.AbsoluteSums.budget_scale (momentWeight_nonneg hs.le _) h) (fun _ => norm_nonneg _) (fun v=>?_); rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left ((league_limit ..).trans (polynomial_cost hs (by positivity) _)) (norm_nonneg _)).trans_eq (by ring)
lemma sums_test (p' : Formula α) (hs : 0<σ) {u : Move α→ℝ} (h : Width σ p u) : Summable fun x:Move α=> u x * lineRead x p' := by
  induction p' using MvPolynomial.induction_on' with
  | monomial d c=> obtain ⟨x,hx,hL⟩:= league_bill d
                   have he : MvPolynomial.monomial d c=C c*league x:=by rw [hL]; simp [MvPolynomial.C_mul_monomial]
                   rw [he]; simp only [lineRead,map_mul,MvPolynomial.eval_C,mul_left_comm (u _) c _]; exact (meters_league x hs h).2.1.of_norm.mul_left _
  | add p q h₁ h₂=> simp_rw [lineRead,map_add,mul_add]; exact h₁.add h₂
-- `total_degree` bounded under rescaling / coordinate collapse. Works for test letters.
omit [Fintype α] in
lemma aeval_downgrade {w : α→ Formula β} (hw : ∀ i,(w i).totalDegree≤1) (f : Formula α) : (MvPolynomial.aeval w f).totalDegree ≤ f.totalDegree := by
  nth_rw 1 [←MvPolynomial.support_sum_monomial_coeff f]; rw [map_sum]; refine sum_cap _ fun i hi=> ?_
  rw [MvPolynomial.monomial_eq,map_mul,MvPolynomial.aeval_C,Finsupp.prod,map_prod]; refine (MvPolynomial.totalDegree_mul ..).trans (le_trans ?_ (MvPolynomial.le_totalDegree hi))
  rw [show (algebraMap ℝ (Formula β))=C from rfl,MvPolynomial.totalDegree_C,zero_add]; apply (MvPolynomial.totalDegree_finsetProd ..).trans; unfold Finsupp.sum; refine sum_le_sum fun y _=> ?_; rw [map_pow, MvPolynomial.aeval_X]
  exact (MvPolynomial.totalDegree_pow _ _).trans (mul_le_of_le_one_right (Nat.zero_le _) (hw _))
end YM.WilsonBulk.Sheet.Taylor
