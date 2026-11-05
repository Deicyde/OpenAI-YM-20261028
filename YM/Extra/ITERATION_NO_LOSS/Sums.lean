import YM.Bid.Craft
import YM.Next.EXTRACTION.Tails
import YM.Work.F08.Width

/-!
# Absolute budget helpers for the iteration

No formal rearrangement of a non-absolutely convergent series. Uses unnormalized sums.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration
open Lattice Wilson RG
open scoped Topology BigOperators

instance (priority := low) plaq_nonempty : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩

variable {α β : Type*}
def numbering (α : Type*) [Countable α] [Infinite α] : ℕ ≃ α :=
  letI := Classical.choice (nonempty_denumerable α)
  (Denumerable.eqv α).symm

namespace Cost

lemma nonneg {f : α → ℝ} {A : ℝ} (hf : SumBudget f A) : 0 ≤ A := (tsum_nonneg hf.1).trans hf.2.2

lemma enlarge {f : α → ℝ} {A B : ℝ} (h : SumBudget f A) (he : A ≤ B) : SumBudget f B :=
  ⟨h.1,h.2.1,h.2.2.trans he⟩

lemma mono {f g : α → ℝ} {C : ℝ} (hg : SumBudget g C) (hn : ∀ i, 0 ≤ f i) (he : ∀ i, f i ≤ g i) :
    SumBudget f C := YM.Work.F08.budget_minor hg hn he

lemma equiv (e : β ≃ α) {f : α → ℝ} {A : ℝ} (h : SumBudget f A) : SumBudget (fun i => f (e i)) A :=
  ⟨fun i => h.1 (e i),e.summable_iff.2 h.2.1,(e.tsum_eq _).trans_le h.2.2⟩

lemma finite [Fintype α] (a : ℝ) (ha : 0 ≤ a) : SumBudget (fun _ : α => a) (Fintype.card α * a) := by
  exact ⟨fun _ => ha,hasSum_fintype _ |>.summable,by rw [tsum_fintype]; simp⟩

lemma scale {f : α → ℝ} {C : ℝ} (h : SumBudget f C) (a : ℝ) (ha : 0 ≤ a) :
    SumBudget (fun i => a*f i) (a*C) := by
  exact ⟨fun i => mul_nonneg ha (h.1 i),h.2.1.mul_left _,by rw [tsum_mul_left]; gcongr; exact h.2.2⟩

lemma scale' {f : α → ℝ} {C : ℝ} (h : SumBudget f C) (a : ℝ) (ha : 0 ≤ a) :
    SumBudget (fun i => f i*a) (C*a) := by simpa only [mul_comm a] using scale h a ha

lemma sum {f : α ⊕ β → ℝ} {A B : ℝ} (hl : SumBudget (fun i => f (.inl i)) A)
    (hr : SumBudget (fun i => f (.inr i)) B) : SumBudget f (A + B) := by
  refine ⟨fun i => ?_, Summable.sum f hl.2.1 hr.2.1, ?_⟩
  · cases i <;> first | exact hl.1 _ | exact hr.1 _
  rw [Summable.tsum_sum (f:=f) hl.2.1 hr.2.1]; exact add_le_add hl.2.2 hr.2.2

lemma product {F : α × β → ℝ} {f : α → ℝ} {A : ℝ} (hf : SumBudget f A)
    (h : ∀ i, SumBudget (fun j => F (i,j)) (f i)) : SumBudget F A := by
  have hn (p : α × β) : 0 ≤ F p := (h p.1).1 p.2
  have hsum := mono hf (fun i => tsum_nonneg ((h i).1)) (fun i => (h i).2.2)
  have hs := (summable_prod_of_nonneg (f:=F) hn).2 ⟨fun i => (h i).2.1,hsum.2.1⟩
  exact ⟨hn,hs,hs.tsum_prod.trans_le hsum.2.2⟩

lemma sigma {β : α → Type*} {F : (i : α) × β i → ℝ} {f : α → ℝ} {A : ℝ} (hf : SumBudget f A)
    (h : ∀ i, SumBudget (fun j => F ⟨i,j⟩) (f i)) : SumBudget F A := by
  have hn (p) : 0 ≤ F p := (h p.1).1 p.2
  have hsum := mono hf (fun i => tsum_nonneg ((h i).1)) (fun i => (h i).2.2)
  have hs := (summable_sigma_of_nonneg hn).2 ⟨fun i => (h i).2.1,hsum.2.1⟩
  exact ⟨hn,hs,hs.tsum_sigma.trans_le hsum.2.2⟩

lemma prod {f : α → ℝ} {g : α → β → ℝ} {A B : ℝ} (hf : SumBudget f A)
    (hg : ∀ i, SumBudget (g i) B) (hB : 0 ≤ B) : SumBudget (fun p : α × β => f p.1 * g p.1 p.2) (A*B) :=
  product (scale' hf _ hB) (fun i => scale (hg i) _ (hf.1 _))

lemma pi {n : ℕ} {f : Fin n → α → ℝ} {A : Fin n → ℝ} (hf : ∀ i, SumBudget (f i) (A i)) :
    SumBudget (fun p : Fin n → α => ∏ i, f i (p i)) (∏ i, A i) := by
  classical
  induction n with
  | zero =>
    simpa using finite (α:=Fin 0 → α) 1 zero_le_one
  | succ n ih =>
    have he := ih (fun i => hf i.succ)
    have h := equiv (Fin.consEquiv (fun _ => α)).symm (prod (hf 0) (fun _ => he) (nonneg he))
    simp_rw [Fin.prod_univ_succ]; exact h

lemma tsum_pi {n : ℕ} {f : Fin n → α → ℝ} (hf : ∀ i, Summable (fun a => |f i a|)) :
    Summable (fun p : Fin n → α => |∏ i, f i (p i)|) ∧
      (∑' p : Fin n → α, ∏ i, f i (p i)) = ∏ i, ∑' p, f i p := by
  have hs := (pi (A:=fun i => ∑' a, |f i a|) (fun i => ⟨fun _ => abs_nonneg _, hf i, le_rfl⟩)).2.1
  simp_rw [Finset.abs_prod]; refine ⟨hs,?_⟩
  induction n with
  | zero => rw [tsum_fintype]; simp
  | succ n ih =>
    have h' := ih (f:=fun i => f i.succ) (fun i => hf _) (by
      exact (pi (A:=fun i : Fin n => ∑' a, |f i.succ a|)
        fun i => ⟨fun _ => abs_nonneg _, hf _, le_rfl⟩).2.1)
    let e := Fin.consEquiv (n:=n) (fun _ => α)
    let F (p : Fin (n+1) → α) := ∏ i, f i (p i)
    have hF : Summable F := .of_norm (by simpa only [F, Real.norm_eq_abs, Finset.abs_prod] using hs)
    change (∑' p, F p) = _
    rw [← e.tsum_eq F]
    have he : Summable (fun p => F (e p)) := (e.summable_iff (f:=F)).2 hF
    rw [he.tsum_prod, Fin.prod_univ_succ, ← h']
    have H (p : α) (q : Fin n → α) : F (e (p,q)) = f 0 p * ∏ i, f i.succ (q i) := by
      unfold F; rw [Fin.prod_univ_succ]; rfl
    simp_rw [H, tsum_mul_left, tsum_mul_right]

end Cost

/-- A fixed width debit for a length (including zero length) with a prescribed moment. -/
def momentPrice (s : ℕ) (η : ℝ) := Real.exp η * s.factorial / η^s
lemma momentPrice_pos (s : ℕ) {η : ℝ} (hη : 0 < η) : 0 < momentPrice s η := by
  unfold momentPrice; positivity
lemma spendMoment (s : ℕ) {η z : ℝ} (hη : 0 < η) (hz : 0 ≤ z) :
    (1+z)^s ≤ momentPrice s η * Real.exp (η*z) := by
  have h := Real.pow_div_factorial_le_exp (η*(1+z)) (by positivity) s
  rw [mul_pow, mul_add, mul_one, Real.exp_add] at h
  have h' := (div_le_iff₀ (show 0 < (s.factorial:ℝ) by positivity)).mp h
  calc
    _ ≤ (Real.exp η * Real.exp (η*z) * s.factorial) / η^s := (le_div_iff₀ (by positivity)).2 (by rwa [mul_comm])
    _ = _ := by unfold momentPrice; ring
end YM.Extra.Iteration
