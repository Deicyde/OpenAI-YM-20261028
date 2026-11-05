import YM.Bid.Craft
import YM.Corona.Halo
import YM.Next.EXTRACTION.Tails

/-!
# Meeting subsets budget on full supports in a fixed vacuum alphabet

Charge **nonempty** bundles hitting a new support; repeatedly use the
*same* cover exponent (pieces intersect). No extensive volume factor in
the hit/activity constants. Absolute convergence certificates, not junk
`tsum` comparisons. The input price for new atoms will need to pay for the
increased support and the cardinality in the meeting-subset estimate (later
lemmas). Geometric convention of E `ved` as specified in Lattice.Support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {n : Side} {ι : Type*}

theorem sumBudget_mono {a b : ι → ℝ} {c C : ℝ} (h : SumBudget b c) (h0 : ∀ i, 0 ≤ a i) (he : a ≤ b) (hc : c ≤ C) : SumBudget a C := by
  have hs := h.2.1.of_nonneg_of_le h0 he
  exact ⟨h0, hs,(hs.tsum_le_tsum he h.2.1).trans (h.2.2.trans hc)⟩

theorem sumBudget_add {a b : ι → ℝ} {c C : ℝ} (h : SumBudget a c) (he : SumBudget b C) : SumBudget (fun i => a i + b i) (c+C) :=
  ⟨fun i => add_nonneg (h.1 i) (he.1 i),h.2.1.add he.2.1, (h.2.1.tsum_add he.2.1).trans_le (add_le_add h.2.2 he.2.2)⟩

theorem sumBudget_zero {c : ℝ} (h : 0 ≤ c) : SumBudget (0 : ι → ℝ) c := ⟨fun i => le_rfl, summable_zero, by simpa using h⟩

theorem sumBudget_mul_left {a : ι → ℝ} {b c : ℝ} (h : SumBudget a c) (he : 0 ≤ b) : SumBudget (fun i => b * a i) (b*c) :=
  ⟨fun i => mul_nonneg he (h.1 i),h.2.1.mul_left b, (h.2.1.tsum_mul_left b).trans_le (mul_le_mul_of_nonneg_left h.2.2 he)⟩

theorem sumBudget_uncharge {B : BudgetPoint} {X : ι → Support n} {a : ι → ℝ} {c : ℝ} (h : ∀ i, 0 ≤ a i)
    (he : SumBudget (fun i => B.mass (X i) (a i)) c) : SumBudget a c :=
  sumBudget_mono he h (fun i => B.loMass (X i) _ (h i)) le_rfl

/-- Pass through an injected set of actual addresses. -/
theorem sumBudget_pass {κ : Type*} (e : ι ↪ κ) (a : κ → ℝ) {b : ℝ} (h : SumBudget (fun i => a (e i)) b)
    (he : ∀ x, (¬∃ y, e y = x) → a x = 0) : SumBudget a b := by
  have hq : a = Function.extend e (a ∘ e) 0 := by
    funext x; by_cases hx : ∃ y,e y=x
    · obtain ⟨y,rfl⟩ := hx; rw [e.injective.extend_apply]; rfl
    rw [Function.extend_apply' _ _ _ hx,he x hx]; rfl
  have hs : HasSum a (∑' i, a (e i)) := by rw [hq]; exact (hasSum_extend_zero e.injective).2 (by simpa only [e.injective.extend_apply] using! h.2.1.hasSum)
  refine ⟨fun x => ?_,hs.summable,hs.tsum_eq.trans_le h.2.2⟩
  by_cases hx : ∃ y,e y=x
  · obtain ⟨y,rfl⟩ := hx; exact h.1 _
  rw [he x hx]

theorem sumBudget_subtype (p : ι → Prop) {a : ι → ℝ} {c : ℝ} (h : SumBudget a c) : SumBudget (fun i : Subtype p => a i.val) c :=
  ⟨fun _ => h.1 _, h.2.1.subtype _, (h.2.1.tsum_subtype_le a {i | p i} h.1).trans h.2.2⟩

theorem sumBudget_sigma {κ : ι → Type*} {f : Sigma κ → ℝ} {a : ι → ℝ} {b : ℝ} (h : ∀ i, SumBudget (fun j => f ⟨i,j⟩) (a i))
    (he : SumBudget a b) : SumBudget f b := by
  have hp := sumBudget_mono he (fun i => tsum_nonneg (h i).1) (fun i => (h i).2.2) le_rfl
  have h0 (i : Sigma κ) := (h i.1).1 i.2
  have hs := (summable_sigma_of_nonneg h0).2 ⟨fun i => (h i).2.1,hp.2.1⟩
  exact ⟨h0,hs,hs.tsum_sigma.trans_le hp.2.2⟩

open scoped Classical in
theorem sumBudget_exponential {a : ι → ℝ} {b : ℝ} (h : SumBudget a b) :
    SumBudget (fun q : Finset ι => if q.Nonempty then ∏ i ∈ q, a i else 0) (Real.exp b - 1) := by
  classical
  let f (q : Finset ι) := ∏ i∈q, a i
  have hf := summable_finsetProd_of_summable_nonneg h.1 h.2.1
  let g (q : Finset ι) := if q.Nonempty then f q else 0
  change SumBudget g _
  have hF (q) : 0 ≤ f q := Finset.prod_nonneg fun i _ => h.1 i
  have hg (q) : 0 ≤ g q := by unfold g; split <;> first | exact hF _ | rfl
  have hgs : Summable g := hf.of_nonneg_of_le hg (fun q => by unfold g; split <;> first | exact hF _ | rfl)
  let u (q : Finset ι) := if q=∅ then (1:ℝ) else 0
  have hu : Summable u := summable_of_ne_finset_zero (s:={∅}) (fun i hi => by simp_all [u])
  have hU : ∑' i, u i = 1 := by rw [tsum_eq_single ∅ (by intro i hi; exact if_neg hi)]; exact if_pos rfl
  have he : ∑' q, f q = (∑' q, g q)+1 := by
    rw [← hU,← hgs.tsum_add hu]; refine tsum_congr fun i => ?_
    by_cases hi : i=∅ <;> simp [g,f,u,Finset.nonempty_iff_ne_empty,hi]
  refine ⟨hg,hgs, le_sub_iff_add_le.mpr (he ▸ ?_)⟩
  rw [← tprod_one_add hf]
  apply le_trans _ (Real.exp_le_exp.mpr h.2.2)
  exact le_of_tendsto_of_tendsto' (Real.multipliable_one_add_of_summable h.2.1).hasProd h.2.1.hasSum.rexp
    (fun s => Finset.prod_le_prod (fun i _ => by linarith [h.1 i]) (fun i _ => (add_comm ..).trans_le (Real.add_one_le_exp _)))

open scoped Classical in
theorem sumBudget_meeting {X : ι → Support n} (Z : Support n) {a : ι → ℝ} {c : ℝ} (hp : ∀ i, 0 ≤ a i)
    (h : ∀ x : Site n, SumBudget (fun i => if x∈ X i then a i else 0) c) :
    SumBudget (fun i => if Disjoint Z (X i) then 0 else a i) ((Z.card:ℝ)*c) := by
  classical
  let f (x : Site n) (i : ι) := if x∈ X i then a i else 0
  have he : SumBudget (fun i => ∑ x∈Z, f x i) ((Z.card:ℝ)*c) := by
    have hs (x) (_ : x∈ Z) : Summable (f x) := (h x).2.1
    exact ⟨fun i => Finset.sum_nonneg (fun x _ => (h x).1 i), summable_sum hs,
      (Summable.tsum_finsetSum hs).trans_le (by simpa using Finset.sum_le_sum (s:=Z) (fun x hx => (h x).2.2))⟩
  apply sumBudget_mono he (fun i => by split <;> first | exact hp _ | rfl) ?_ le_rfl
  intro i; dsimp only; split
  · exact he.1 _
  rename_i hN; obtain ⟨x,hx,hy⟩ := Finset.not_disjoint_iff.mp hN
  simpa only [f,if_pos hy] using Finset.single_le_sum (f:=fun x => f x i) (fun x _ => (h x).1 i) hx

variable {B : BudgetPoint}

theorem cover_union_meeting (b : ℕ) (Z : Support n) (X : ι → Support n) (q : Finset ι) (h : ∀ i∈q, ¬Disjoint Z (X i)) :
    coverNumber b (Z∪q.biUnion X) ≤ coverNumber b Z + ∑ i∈q, coverNumber b (X i) := by
  classical
  induction q using Finset.induction_on with
  | empty => simp
  | insert i q hi ih =>
    obtain ⟨x,hx,hy⟩ := Finset.not_disjoint_iff.mp (h i (by simp))
    rw [Finset.biUnion_insert, Finset.union_left_comm, Finset.sum_insert hi, add_left_comm]
    exact (Corona.meets_sum hy (Finset.mem_union_left _ hx) b).trans (Nat.add_le_add_left (ih fun j hj => h j (by simp [hj])) _)

theorem mass_union_meeting (Z : Support n) (X : ι → Support n) (q : Finset ι) (h : ∀ i∈q, ¬Disjoint Z (X i)) (a : ι → ℝ) (c : ℝ)
    (ha : ∀ i∈q, 0 ≤ a i) (hc : 0 ≤ c) (B : BudgetPoint) :
    B.mass (Z∪q.biUnion X) (c * ∏ i ∈ q, a i) ≤ B.mass Z c * ∏ i∈q, B.mass (X i) (a i) := by
  simp only [BudgetPoint.mass, Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
  rw [mul_mul_mul_comm (Real.exp _) c, ← Real.exp_add, ← mul_add]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast cover_union_meeting B.B Z X q h) B.exponent_pos.le)) (mul_nonneg hc (Finset.prod_nonneg ha))
end YM.Push.Local
