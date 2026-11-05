import YM.Next.MULTISOURCE.Curves


set_option warningAsError false

/-!
# Absolute series budget helpers

For the conditional scalar vacuum stability project. No conditionally convergent rearrangements -- we
want equalities of actual unnormalized densities and even the output **letters** in their actual
history. Keep budgets in `SumBudget`; all number series with unspecified filter use unordered sums.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi.Vacuum
open RG Lattice Wilson Filter Finset Function MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

namespace Absolute
variable {I J : Type*} {K : I → Type*}

lemma bound_nonneg {f : I → ℝ} {c : ℝ} (h : SumBudget f c) : 0 ≤ c :=
  (tsum_nonneg h.1).trans h.2.2

lemma loosen {f : I → ℝ} {c d : ℝ} (h : SumBudget f c) (hd : c ≤ d) : SumBudget f d :=
  ⟨h.1,h.2.1,h.2.2.trans hd⟩

lemma compare {f g : I → ℝ} {c : ℝ} (h : SumBudget f c)
    (hg : ∀ i, 0 ≤ g i) (hh : ∀ i, g i ≤ f i) : SumBudget g c :=
  permit_le h le_rfl fun i => ⟨hg i, hh i⟩

lemma singleton (x : ℝ) (hx : 0 ≤ x) : SumBudget (fun _ : Unit => x) x := by
  simp [SumBudget,hx]
  exact (hasSum_fintype _).summable

lemma empty (x : Empty → ℝ) : SumBudget x 0 := by
  simp [SumBudget]

lemma union {f : I ⊕ J → ℝ} {c d : ℝ} (h : SumBudget (f ∘ Sum.inl) c)
    (h' : SumBudget (f ∘ Sum.inr) d) : SumBudget f (c+d) := by
  have he := HasSum.sum (f:=f) h.2.1.hasSum h'.2.1.hasSum
  refine ⟨?_,he.summable,he.tsum_eq.trans_le (add_le_add h.2.2 h'.2.2)⟩
  rintro (i|j)
  · exact h.1 _
  exact h'.1 _

lemma union_tsum {f : I ⊕ J → ℂ} (h : Summable (f ∘ Sum.inl))
    (h' : Summable (f ∘ Sum.inr)) :
    ∑' i, f i = (∑' i, f (.inl i))+ ∑' i, f (.inr i) := (HasSum.sum (f:=f) h.hasSum h'.hasSum).tsum_eq

lemma bundles {f : Sigma K → ℝ} {q : I → ℝ} {c : ℝ} (h : SumBudget q c)
    (hg : ∀ i, SumBudget (fun j => f ⟨i,j⟩) (q i)) : SumBudget f c := by
  have hh (b : Sigma K) : 0 ≤ f b := (hg b.1).1 b.2
  have he : SumBudget (fun i => ∑' j, f ⟨i,j⟩) c := compare h
    (fun i => tsum_nonneg (hg i).1) fun i => (hg i).2.2
  have hf := (summable_sigma_of_nonneg hh).2 ⟨fun i => (hg i).2.1, he.2.1⟩
  exact ⟨hh,hf,hf.tsum_sigma.trans_le he.2.2⟩

lemma cross {f : I → ℝ} {g : J → ℝ} {a b : ℝ} (h : SumBudget f a) (h' : SumBudget g b) :
    SumBudget (fun i : I × J => f i.1 * g i.2) (a*b) := by
  have hf := h.2.1.norm
  have hg := h'.2.1.norm
  exact ⟨fun i => mul_nonneg (h.1 _) (h'.1 _),summable_mul_of_summable_norm hf hg,
    (tsum_mul_tsum_of_summable_norm hf hg).symm.trans_le (mul_le_mul h.2.2 h'.2.2 (tsum_nonneg h'.1) (bound_nonneg h))⟩

lemma little {f : I → ℝ} {c : ℝ} (h : SumBudget f c) (i : I) : f i ≤ c := by
  apply le_trans _ h.2.2
  simpa only [Finset.sum_singleton] using h.2.1.sum_le_tsum {i} (fun j _ => h.1 j)

lemma cexp (z : ℂ) : HasSum (fun n : ℕ => ((n.factorial:ℂ)⁻¹)*z^n) (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  simpa only [div_eq_mul_inv, mul_comm ((_:ℂ)⁻¹)] using NormedSpace.expSeries_div_hasSum_exp z

lemma rexp (x : ℝ) (hx : 0 ≤ x) : SumBudget (fun n : ℕ => ((n.factorial:ℝ)⁻¹)*x^n) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  have h : HasSum (fun n : ℕ => ((n.factorial:ℝ)⁻¹)*x^n) (NormedSpace.exp x) := by
    simpa only [div_eq_mul_inv,mul_comm ((_:ℝ)⁻¹)] using NormedSpace.expSeries_div_hasSum_exp x
  exact ⟨fun i => by positivity,h.summable,h.tsum_eq.le⟩

lemma clog {z : ℂ} (hz : ‖z‖ < 1) : HasSum (fun n : ℕ =>
    ((-1:ℂ)^(n+2)/(↑(n+1:ℕ):ℂ))*z^(n+1)) (Complex.log (1+z)) := by
  have he := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_taylorSeries_log hz)
  simpa [div_eq_mul_inv, mul_right_comm] using he

lemma geometric {x : ℝ} (hx : 0 ≤ x) (he : x ≤ 1/2) : SumBudget (fun n : ℕ => x^(n+1)) (2*x) := by
  have ht : ‖x‖ < 1 := by rw [Real.norm_of_nonneg hx]; linarith
  have h : HasSum (fun n : ℕ => x^(n+1)) ((1-x)⁻¹*x) := by
    simpa only [pow_succ] using (hasSum_geometric_of_norm_lt_one ht).mul_right x
  refine ⟨fun i => pow_nonneg hx _, h.summable,h.tsum_eq.trans_le ?_⟩
  gcongr
  rw [inv_le_iff_one_le_mul₀] <;> linarith

/-! Number hit norms measured with actual `coverNumber`. -/
section
variable {n : Side} {X : I → Support n} {M : ℕ} {a γ : ℝ} {f : I → ℝ}

lemma burden (h : ∀ i, (X i).Nonempty) (hh : Ac.Hit X M f a γ) :
    (∀ i, 0 ≤ f i) ∧ Summable (fun i => f i*Real.exp (a*coverNumber M (X i))) := by
  let q := fun i => f i*Real.exp (a*coverNumber M (X i))
  let g := fun x i => if x ∈ X i then q i else 0
  have ht i : 0 ≤ q i := by
    obtain ⟨x,hx⟩ := h i
    simpa only [if_pos hx,q] using (hh x).1 i
  refine ⟨fun i => nonneg_of_mul_nonneg_left (ht i) (Real.exp_pos _),?_⟩
  have hs : Summable fun i => ∑ x : Site n, g x i := summable_sum fun x _ => (hh _).2.1
  apply hs.of_nonneg_of_le ht
  intro i; obtain ⟨x,hx⟩ := h i; exact le_trans (le_of_eq (show q i = g x i from (if_pos hx).symm))
    (Finset.single_le_sum (f:=fun y => g y i) (fun y _ => (hh y).1 i) (Finset.mem_univ _))

lemma relax (h : Ac.Hit X M f a γ) {g : I → ℝ} {b δ : ℝ} (hd : γ ≤ δ)
    (hg : ∀ i, 0 ≤ g i) (hl : ∀ i, g i ≤ f i) (hb : b ≤ a) : Ac.Hit X M g b δ := by
  intro x; apply loosen _ hd; apply compare (h x)
  · intro i; split
    · exact mul_nonneg (hg _) (Real.exp_pos _).le
    exact le_rfl
  intro i; split
  · apply mul_le_mul (hl _) _ (Real.exp_pos _).le ((hg i).trans (hl i))
    gcongr
  exact le_rfl

lemma account (h : ∀ i, (X i).Nonempty) (hh : Ac.Hit X M f a γ) (ha : 0 ≤ a) : Summable f := by
  simpa using (burden h (relax hh le_rfl (burden h hh).1 (fun _ => le_rfl) ha)).2
end

end Absolute
end YM.Multi.Vacuum
