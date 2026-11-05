import YM.Ac.Table
import YM.RG.Activities

/-!
# Receipts for absolute sums

All series bounds in this module use **unconditional absolute sums over actual
addresses**. We deal in `YM.RG.SumBudget`, which gives summability as well as
an inequality. In particular when we use a degree or a fiber estimate, it is
an estimate on sums including ALL label multiplicities (conveniently: on all
finite subsums). No positivity of a physical amplitude is implicit. These
lemmas are for its nonnegative majorant.

A degree tail always includes equality at the cut. Price-tail and polynomial
variants consume an explicit exponent reserve.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums

open YM.RG Filter Finset
open scoped Topology BigOperators Classical

section Budget
variable {ι κ : Type*}
variable {f g : ι → ℝ} {C D : ℝ}

lemma budget_sum (h : SumBudget f C) (s : Finset ι) : ∑ i ∈ s, f i ≤ C :=
  (h.2.1.sum_le_tsum s (fun i _ => h.1 i)).trans h.2.2

lemma budget_of_sum (hf : ∀ i, 0 ≤ f i) (h : ∀ s : Finset ι, ∑ i ∈ s, f i ≤ C) :
    SumBudget f C := by
  have he : Summable f := summable_of_sum_le hf h
  exact ⟨hf, he, he.tsum_le_of_sum_le h⟩

lemma budget_finite [Fintype ι] (hf : ∀ i, 0 ≤ f i) (h : ∑ i, f i ≤ C) :
    SumBudget f C := budget_of_sum hf fun s =>
  (sum_le_sum_of_subset_of_nonneg (subset_univ s) fun i _ _ => hf i).trans h

lemma budget_nonneg (h : SumBudget f C) : 0 ≤ C := by simpa using budget_sum h ∅

lemma budget_single (h : SumBudget f C) (i : ι) : f i ≤ C := by
  simpa using budget_sum h {i}

lemma budget_loosen (h : SumBudget f C) (he : C ≤ D) : SumBudget f D :=
  ⟨h.1, h.2.1, h.2.2.trans he⟩

lemma budget_mono (h : SumBudget f C) (hg : ∀ i, 0 ≤ g i) (he : ∀ i, g i ≤ f i) :
    SumBudget g C := budget_of_sum hg fun s =>
  (sum_le_sum (fun i _ => he i)).trans (budget_sum h s)

lemma budget_scale {x : ℝ} (hx : 0 ≤ x) (h : SumBudget f C) :
    SumBudget (fun i => x * f i) (x * C) := by
  refine budget_of_sum (fun i => mul_nonneg hx (h.1 i)) fun s => ?_
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (budget_sum h s) hx

lemma budget_plus (h : SumBudget f C) (he : SumBudget g D) :
    SumBudget (fun i => f i + g i) (C + D) := by
  refine budget_of_sum (fun i => add_nonneg (h.1 i) (he.1 i)) fun s => ?_
  rw [sum_add_distrib]
  exact add_le_add (budget_sum h s) (budget_sum he s)

lemma budget_over (s : Finset κ) (b : κ → ι → ℝ) (c : κ → ℝ)
    (h : ∀ k ∈ s, SumBudget (b k) (c k)) :
    SumBudget (fun i => ∑ k ∈ s, b k i) (∑ k ∈ s, c k) := by
  refine budget_of_sum (fun i => sum_nonneg (fun k hk => (h k hk).1 i)) fun t => ?_
  rw [sum_comm]
  exact sum_le_sum fun k hk => budget_sum (h k hk) t



lemma budget_pull {w : κ → ℝ} (b : ι → κ) (he : Function.Injective b) (h : SumBudget w C) :
    SumBudget (fun i => w (b i)) C := by
  refine budget_of_sum (fun i => h.1 _) fun s => ?_
  calc
    _ = ∑ k ∈ s.image b, w k := (sum_image he.injOn).symm
    _ ≤ C := budget_sum h _

/-- A uniform multiplicity receipt. Choices that survive as distinct labels
must ALL be priced, even variants with the same physical footprint. -/
lemma budget_fiberwise {W : κ → ℝ} (p : ι → κ) (hf : ∀ i, 0 ≤ f i)
    (hh : ∀ (k : κ) (s : Finset ι), (∀ i ∈ s, p i = k) → ∑ i ∈ s, f i ≤ W k)
    (h : SumBudget W C) : SumBudget f C := by
  refine budget_of_sum hf fun s => ?_
  calc
    _ = ∑ k ∈ s.image p, ∑ i ∈ s with p i = k, f i :=
      (sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem p hi) _).symm
    _ ≤ _ := (sum_le_sum fun k _ => hh k _ fun _ hi => (mem_filter.mp hi).2).trans
      (budget_sum h _)



lemma budget_prod {W : κ → ℝ} (h : SumBudget f C) (H : SumBudget W D) :
    SumBudget (fun i : ι × κ => f i.1 * W i.2) (C * D) := by
  have hv (i : ι × κ) : 0 ≤ f i.1 * W i.2 := mul_nonneg (h.1 _) (H.1 _)
  refine budget_of_sum hv fun s => ?_
  let u := s.image Prod.fst
  let v := s.image Prod.snd
  calc
    _ ≤ ∑ i ∈ u ×ˢ v, f i.1 * W i.2 := sum_le_sum_of_subset_of_nonneg (fun i hi =>
      mem_product.mpr ⟨mem_image_of_mem _ hi, mem_image_of_mem _ hi⟩) fun i _ _ => hv i
    _ = (∑ i ∈ u, f i) * ∑ i ∈ v, W i := by rw [sum_product, sum_mul]; simp only [mul_sum]
    _ ≤ _ := mul_le_mul (budget_sum h u) (budget_sum H v)
      (sum_nonneg fun i _ => H.1 _) (budget_nonneg h)

end Budget

section Tails
variable {ι : Type*} {f : ι → ℝ} {C q : ℝ}

lemma budget_geometric (hC : 0 ≤ C) (hq : 0 ≤ q) (h : q < 1) :
    SumBudget (fun k : ℕ => C * q^k) (C * (1-q)⁻¹) :=
  budget_scale hC ⟨fun _ => pow_nonneg hq _, summable_geometric_of_lt_one hq h,
    (tsum_geometric_of_lt_one hq h).le⟩

/-- Sum all address degeneracies. Estimates at a fixed degree on ALL
finite subsums give an exponential absolute tail, including its boundary. -/
lemma budget_degrees_tail (d : ι → ℕ) (hf : ∀ i, 0 ≤ f i) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (h : q < 1)
    (hb : ∀ (k : ℕ) (s : Finset ι), (∀ i ∈ s, d i = k) → ∑ i ∈ s, f i ≤ C * q^k)
    (m : ℕ) : SumBudget (fun i => if m ≤ d i then f i else 0) (C * q^m * (1-q)⁻¹) := by
  let g := fun i => if m ≤ d i then f i else 0
  have hg i : 0 ≤ g i := by unfold g; split <;> first | exact hf i | exact le_rfl
  refine budget_fiberwise (fun i => d i - m) hg (fun k s hk => ?_)
    (budget_geometric (mul_nonneg hC (pow_nonneg hq m)) hq h)
  simp only [← sum_filter]
  have he i (hi : i ∈ s.filter (fun i => m ≤ d i)) : d i = m+k := by
    obtain ⟨h1,h2⟩ := mem_filter.mp hi
    specialize hk i h1
    omega
  simpa only [pow_add,mul_assoc] using hb (m+k) _ he

lemma budget_degrees (d : ι → ℕ) (hf : ∀ i, 0 ≤ f i) (hC : 0 ≤ C) (hq : 0 ≤ q) (h : q < 1)
    (hb : ∀ (k : ℕ) (s : Finset ι), (∀ i ∈ s, d i = k) → ∑ i ∈ s, f i ≤ C * q^k) :
    SumBudget f (C * (1-q)⁻¹) := by
  simpa using budget_degrees_tail d hf hC hq h hb 0

/-- Simple entropy-vs-size test using counts per degree of *live*
addresses (labels with nonzero weight). For example a count of at most
`A * B^k` and a weight of at most `C * r^k`; `q` can be a convenient
upper bound for `B * r`. Includes infinitely many zero entries. -/
lemma budget_count_tail (d : ι → ℕ) (hf : ∀ i, 0 ≤ f i) (hC : 0 ≤ C)
    {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hi : ∀ i, f i ≤ C * r^(d i))
    (hb : ∀ (k : ℕ) (s : Finset ι), (∀ i ∈ s, d i = k ∧ f i ≠ 0) → s.card ≤ A * B^k)
    (hq : B * r ≤ q) (h : q < 1) (m : ℕ) :
    SumBudget (fun i => if m ≤ d i then f i else 0) ((A*C)*q^m*(1-q)⁻¹) := by
  apply budget_degrees_tail d hf (mul_nonneg hA hC) ((mul_nonneg hB hr).trans hq) h _ m
  intro k s hk
  let t := s.filter (fun i => f i ≠ 0)
  have he i (hh : i ∈ t) : d i = k ∧ f i ≠ 0 :=
    ⟨hk _ (mem_filter.mp hh).1, (mem_filter.mp hh).2⟩
  calc
    _ = ∑ i∈t, f i := (sum_subset (filter_subset ..) (fun i hh hj => by
        by_contra hz
        exact hj (mem_filter.mpr ⟨hh,hz⟩))).symm
    _ ≤ ∑ _i∈t, C*r^k := sum_le_sum fun i hh => by simpa only [(he i hh).1] using hi i
    _ = t.card * (C*r^k) := by simp
    _ ≤ A * B^k * (C*r^k) := mul_le_mul_of_nonneg_right (hb k t he) (by positivity)
    _ = A*C*(B*r)^k := by ring
    _ ≤ A*C*q^k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hB hr) hq k)
      (mul_nonneg hA hC)







lemma polynomial_price {p a : ℝ} (ha : 0 < a) (hp : 0 ≤ p) (k : ℕ) :
    p^k ≤ a⁻¹^k * k.factorial * Real.exp (a*p) := by
  have hK : 0 < (k.factorial : ℝ) := by positivity
  calc
    _ = a⁻¹^k * ((a*p)^k / k.factorial * k.factorial) := by rw [mul_pow,inv_pow]; field_simp
    _ ≤ a⁻¹^k * (Real.exp (a*p) * k.factorial) := by
      gcongr
      exact Real.pow_div_factorial_le_exp _ (by positivity) k
    _ = _ := by ring

lemma polynomial_cost {p a : ℝ} (ha : 0 < a) (hp : 0 ≤ p) (k : ℕ) :
    (1+p)^k ≤ (a⁻¹^k * k.factorial * Real.exp a) * Real.exp (a*p) := by
  simpa only [mul_add,mul_one,Real.exp_add,mul_assoc] using
    polynomial_price ha (show 0 ≤ 1+p by positivity) k


end Tails

end YM.Push.AbsoluteSums
