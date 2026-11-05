import YM.Push.ABSOLUTE_SUMS.Clusters

/-!
# MANY-component products and the volume factor

per-site budgets can be summed at each finite volume; bound
the resulting absolute product series by an exponential. Thus estimates
*uniform in volume* in the sense of a uniform per-site cost/log-cost,
not bounding an unrooted extensive sum by a CONSTANT. Such a bound is
false; also not rescued by requiring just ONE component hit and allowing
arbitrary other components. Contrast with the external-root estimates of
`Forest` and `Distinct` in which each component pays a root. We include
direct obstructions below. We also show costs of empty-address conventions:
though actual activity/address types come with anchors or compulsory flag
sets, no recovery of an empty-support budget from hits when testing general
series. Include empty forests (the product contribution is one).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Product
open Trees Ursell RG Lattice Finset Animals
open scoped Classical Topology BigOperators
variable {ι : Type*} {n : Side}

section Extensive

lemma everyone (X : ι → Support n) (M : ℕ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {a c b : ℝ} (h : Ac.Hit X M w a c) (he : SumBudget (fun i => if X i = ∅ then w i else 0) b) :
    SumBudget (charge X M w a) (b+(n.val^4:ℕ)*c) := by
  let f (x : Site n) i := if x∈X i then charge X M w a i else 0
  have hh : SumBudget (fun i => ∑ x : Site n, f x i) ((n.val^4:ℕ)*c) := by
    convert budget_over univ f (fun _ => c) (fun x _ => h x) using 1
    simp
  have hh := budget_plus he hh
  refine budget_mono hh (charge_pos X M hw a) fun i => ?_
  rcases (X i).eq_empty_or_nonempty with hi|hi
  · simp [hi,f,charge,currency,Animals.price_zero]
  obtain ⟨x,hx⟩ := hi
  have ht : f x i ≤ ∑ y, f y i := single_le_sum (fun y _ => (h y).1 i) (mem_univ x)
  simpa only [f, if_pos hx, if_neg (show X i ≠ ∅ from Finset.Nonempty.ne_empty ⟨x,hx⟩),zero_add]
    using ht

lemma everyone_ne (X : ι → Support n) (M : ℕ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, w i ≠ 0 → (X i).Nonempty) {a c : ℝ} (h : Ac.Hit X M w a c) :
    SumBudget (charge X M w a) ((n.val^4:ℕ)*c) := by
  have he i : (if X i = ∅ then w i else 0)=0 := by
    split
    next he => by_contra hh; simpa only [he,Finset.not_nonempty_empty] using hv i hh
    next he => rfl
  simpa only [zero_add] using everyone X M hw h (b:=0) (by
    simp only [he]; exact budget_of_sum (fun i => le_rfl) fun i => by rw [sum_const_zero])

lemma set_products {C : ℝ} {f : ι → ℝ} (h : SumBudget f C) : SumBudget
    (fun s : Finset ι => ∏ i∈s, f i) (Real.exp C) := by
  have hf s : 0 ≤ ∏ i∈s, f i := prod_nonneg fun i _ => h.1 i
  refine budget_of_sum hf fun t => ?_
  let u := t.biUnion id
  calc
    _ ≤ ∑ s∈u.powerset, ∏ i∈s, f i := sum_le_sum_of_subset_of_nonneg (fun s hs =>
      mem_powerset.mpr fun i hi => mem_biUnion.mpr ⟨s,hs,hi⟩) fun i _ _ => hf i
    _ = ∏ i∈u, (f i + 1) := (prod_add_one u).symm
    _ ≤ ∏ i∈u, Real.exp (f i) := prod_le_prod (fun i _ => add_nonneg (h.1 i) zero_le_one) fun i _ =>
      Real.add_one_le_exp _
    _ ≤ _ := by rw [← Real.exp_sum]; exact Real.exp_monotone (budget_sum h u)










end Extensive

section Empty









end Empty

section Obstruction




end Obstruction
end YM.Push.AbsoluteSums.Product
