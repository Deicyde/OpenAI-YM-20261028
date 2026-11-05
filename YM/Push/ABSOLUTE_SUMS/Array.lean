import YM.Push.ABSOLUTE_SUMS.Basic

/-! # Helpers for occurrence budgets
Alphabets may always have multiple/infinitely many labels; lift from
uniform receipts on all finite subpopulations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums
open RG Finset
open scoped BigOperators Topology Classical

variable {κ ι : Type*}

lemma sigma_fixed {β : κ → Type*} (b : Sigma β → ℝ) (k : κ) {c : ℝ}
    (h : SumBudget (fun i : β k => b ⟨k,i⟩) c) (s : Finset (Sigma β))
    (hs : ∀ i∈s, i.1=k) : ∑ i∈s, b i ≤ c := by
  let e : β k ↪ Sigma β := Function.Embedding.sigmaMk k
  let t := s.preimage e e.injective.injOn
  have he : t.image e = s := by
    ext i; rw [mem_image]; constructor
    · rintro ⟨i,hi,rfl⟩
      exact mem_preimage.mp hi
    intro hi; obtain ⟨k',l⟩ := i
    have ht : k'=k := hs _ hi
    subst k'
    exact ⟨l,mem_preimage.mpr hi,rfl⟩
  calc
    _ = ∑ i∈t, b (e i) := by nth_rewrite 1 [← he]; rw [sum_image e.injective.injOn]
    _ ≤ _ := budget_sum h t

lemma sigma_total {β : κ → Type*} (b : Sigma β → ℝ) (c : κ → ℝ)
    (hb : ∀ k : κ, SumBudget (fun i : β k => b ⟨k,i⟩) (c k)) {C : ℝ} (h : SumBudget c C) :
    SumBudget b C := budget_fiberwise Sigma.fst (fun i => (hb i.1).1 i.2)
      (fun k s hs => sigma_fixed b k (hb k) s hs) h

lemma budget_rows (b : κ × ι → ℝ) (c : κ → ℝ)
    (hb : ∀ k, SumBudget (fun i : ι => b (k,i)) (c k)) {C : ℝ} (h : SumBudget c C) :
    SumBudget b C := by
  let e := Equiv.sigmaEquivProd κ ι
  have he := sigma_total (b ∘ e) c hb h
  simpa only [Function.comp_apply,e.apply_symm_apply] using budget_pull e.symm e.symm.injective he

lemma sigma_tail {β : ℕ → Type*} (b : Sigma β → ℝ) {C q : ℝ}
    (hb : ∀ k, SumBudget (fun i => b ⟨k,i⟩) (C*q^k))
    (hC : 0 ≤ C) (hq : 0 ≤ q) (h : q < 1) (m : ℕ) :
    SumBudget (fun i => if m ≤ i.1 then b i else 0) (C*q^m*(1-q)⁻¹) :=
    budget_degrees_tail Sigma.fst (fun i => (hb i.1).1 i.2) hC hq h (fun k s hs =>
      sigma_fixed b k (hb k) s hs) m

lemma budget_assignments {α : Type*} [Fintype α] [DecidableEq α] [Fintype κ] (b : κ × (α → ι) → ℝ)
    (hb : ∀ i, 0 ≤ b i) {C : ℝ}
    (h : ∀ D : Finset ι, ∑ i, ∑ j : α → D, b (i,fun l => (j l).val) ≤ C) :
    SumBudget b C := by
  apply budget_of_sum hb; intro s
  let D := s.biUnion (fun i => univ.image i.2)
  let f := fun i : κ × (α → D) => (i.1,(fun l => (i.2 l).val))
  have he : Function.Injective f := by
    rintro ⟨a,i⟩ ⟨c,j⟩ h
    refine Prod.ext (show a = c from congr_arg Prod.fst h) (funext fun x => ?_)
    exact Subtype.ext (congr_fun (congr_arg Prod.snd h) x)
  calc
    _ ≤ ∑ i∈univ.image f,b i := by
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hb i)
      intro i hi
      have h (l : α) : i.2 l ∈ D := mem_biUnion.mpr ⟨i,hi,mem_image_of_mem _ (mem_univ _)⟩
      exact mem_image.mpr ⟨(i.1, fun l => ⟨i.2 l,h l⟩),mem_univ _,rfl⟩
    _ ≤ _ := by rw [sum_image he.injOn,Fintype.sum_prod_type]; exact h D

end YM.Push.AbsoluteSums
