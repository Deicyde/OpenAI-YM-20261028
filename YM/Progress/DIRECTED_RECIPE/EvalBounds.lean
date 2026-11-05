import YM.Progress.DIRECTED_RECIPE.Motion

/-!
# Quantitative continuity through the actual (hard and soft) evaluation

Continuity of the represented rep is E/K charged as an all-address
sup perturbation. Product of K terms is not independent on differently
flagged cylinders; to evaluate at V, compare BOTH representatives there.
Witnesses for packs *coincide* since the dictionaries do. We get a bound
independent of configuration using this charge and the total K expense at the
base parameter. This is a volume-dependent analysis (e.g., when realizing
a Curve for shooting); don't infer the incoming costs in RAdvances from it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe
open Function Set RG Wilson Lattice RG.Shoot MeasureTheory Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius

namespace Payment
open Finset
section finite
variable {a b p q : ℕ → ℝ}

private lemma prod_delta (h : ∀ i, ‖a i‖ ≤ p i) (hk : ∀ i, ‖a i-b i‖ ≤ q i) (s : Finset ℕ) :
    ‖(∏ i∈s, a i)-∏ i∈s,b i‖ ≤ (∏ i∈s, (p i+q i))- ∏ i∈s, p i := by
  have hp j : 0 ≤ p j := (norm_nonneg _).trans (h j)
  have hq j : 0 ≤ q j := (norm_nonneg _).trans (hk j)
  have hf j : ‖b j‖ ≤ p j + q j := by
    calc
      _ = ‖a j - (a j-b j)‖ := by ring_nf
      _ ≤ ‖a j‖ + ‖a j-b j‖ := norm_sub_le ..
      _ ≤ _ := add_le_add (h j) (hk j)
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    let A := ∏ j∈s, a j
    let B := ∏ j∈s, b j
    let C := ∏ j∈s,(p j+q j)
    let D := ∏ j∈s,p j
    have he : ‖B‖ ≤ C := by
      unfold B C; rw [norm_prod]
      exact prod_le_prod (fun j _ => norm_nonneg _) fun j _ => hf j
    simp only [prod_insert hi]
    calc
      _ = ‖a i*(A-B)+(a i-b i)*B‖ := by unfold A B; ring_nf
      _ ≤ ‖a i*(A-B)‖+‖(a i-b i)*B‖ := norm_add_le ..
      _ ≤ p i*(C-D)+q i*C := by
        rw [norm_mul,norm_mul]; exact add_le_add
          (mul_le_mul (h i) ih (norm_nonneg _) (hp i))
          (mul_le_mul (hk i) he (norm_nonneg _) (hq i))
      _ = _ := by unfold C D; ring

private lemma fin_products {c d : ℝ} (h : SumBudget p c) (hg : SumBudget q d) (s : Finset ℕ) :
    ∑ i∈s.powerset, ((∏ j∈i, (p j + q j)) - ∏ j∈i, p j) ≤ Real.exp c*(Real.exp d - 1) := by
  have ht := Finset.prod_nonneg (s:=s) (f:=fun i => 1+p i) fun i _ => add_nonneg zero_le_one (h.1 i)
  have he : (∏ i∈s, (1 + (p i + q i))) ≤ (∏ i∈s, (1 + p i))*Real.exp d := calc
    _ ≤ ∏ i∈s, (1+p i)*Real.exp (q i) := by
      refine prod_le_prod (fun i _ => add_nonneg zero_le_one (add_nonneg (h.1 i) (hg.1 i))) fun i _ => ?_
      have hn := Real.add_one_le_exp (q i)
      calc
        _ ≤ (1+p i)*(q i+1) := by nlinarith only [mul_nonneg (h.1 i) (hg.1 i)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hn (add_nonneg zero_le_one (h.1 i))
    _ ≤ _ := by
      rw [prod_mul_distrib,← Real.exp_sum]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_monotone ((hg.2.1.sum_le_tsum s (fun i _ => hg.1 i)).trans hg.2.2)) ht
  have hz : (∏ i∈s, (1+p i)) ≤ Real.exp c := calc
    _ ≤ ∏ i∈s, Real.exp (p i) := Finset.prod_le_prod (fun i _ => add_nonneg zero_le_one (h.1 i))
      (fun i _ => by rw [add_comm]; exact Real.add_one_le_exp _)
    _ ≤ _ := by
      rw [← Real.exp_sum]
      exact Real.exp_monotone ((h.2.1.sum_le_tsum s (fun i _ => h.1 i)).trans h.2.2)
  rw [Finset.sum_sub_distrib, ← Finset.prod_one_add (f:=fun i => p i+q i), ← Finset.prod_one_add]
  refine le_trans (sub_le_sub_right he _) (le_trans ?_ (mul_le_mul_of_nonneg_right hz
    (sub_nonneg.mpr (Real.one_le_exp ((tsum_nonneg hg.1).trans hg.2.2)))))
  rw [mul_sub,mul_one]

lemma products {c d : ℝ} (h : SumBudget p c) (hg : SumBudget q d) :
    SumBudget (fun s : Finset ℕ => (∏ i∈s, (p i + q i)) - ∏ i∈s, p i)
      (Real.exp c * (Real.exp d-1)) := by
  let D := fun s : Finset ℕ => (∏ i∈s, (p i + q i)) - ∏ i∈s, p i
  have hs : Summable D := (summable_finsetProd_of_summable_nonneg (fun i => add_nonneg (h.1 i) (hg.1 i))
    (h.2.1.add hg.2.1)).sub (summable_finsetProd_of_summable_nonneg h.1 h.2.1)
  have hv (s : Finset ℕ) : 0 ≤ D s := sub_nonneg.mpr <|
    prod_le_prod (fun i _ => h.1 i) (fun i _ => le_add_of_nonneg_right (hg.1 i))
  refine ⟨hv,hs, hs.tsum_le_of_sum_le fun s => ?_⟩
  let v := s.biUnion id
  exact (sum_le_sum_of_subset_of_nonneg (t:=v.powerset) (fun i hi => mem_powerset.mpr fun j hj =>
    mem_biUnion.mpr ⟨i,hi,hj⟩) (fun i _ _ => hv i)).trans (fin_products h hg v)
end finite

variable {G : Gauge} {n : Side} {P : BudgetPoint}
lemma smaller {ι : Type*} {f g : ι → ℝ} {d : ℝ} (h : SumBudget f d)
    (he : ∀ i, 0 ≤ g i) (hg : ∀ i,g i ≤ f i) : SumBudget g d := by
  have hs := h.2.1.of_nonneg_of_le he hg
  exact ⟨he,hs,(hs.tsum_le_tsum hg h.2.1).trans h.2.2⟩

lemma gas_pay {A B : Activities G n} (h : A.forced=B.forced)
    {p q : ℕ → ℝ} {C d : ℝ} (hc : SumBudget p C) (hd : SumBudget q d) (U : Config G n)
    (hh : ∀ j, ‖A.K j U‖ ≤ p j)
    (hk : ∀ i, ‖A.K i U-B.K i U‖ ≤ q i) (P : BudgetPoint) :
    SumBudget (fun b : Finset ℕ => ‖A.gasOccurrence P b U - B.gasOccurrence P b U‖)
      (Real.exp C * (Real.exp d-1)) := by
  classical
  apply smaller (products hc hd) (fun _ => norm_nonneg _)
  intro b
  have hx : A.admissible P U b ↔ B.admissible P U b := by unfold Activities.admissible; rw [h]
  simp only [Activities.gasOccurrence,hx]; split_ifs with H
  · exact prod_delta hh hk _
  · simpa only [sub_zero,norm_zero] using (products hc hd).1 b

lemma masked_pay {A B : Activities G n} (h : A.reg=B.reg)
    {e : ℕ → ℝ} {C : ℝ} (he : ∀ i, variesRegular P (A.reg i) (A.E i) (B.E i) (e i))
    (hg : SumBudget (fun i => P.mass (A.reg i).support (e i)) C) (U : Config G n) :
    SumBudget (fun i => ‖A.regularOccurrence P i U - B.regularOccurrence P i U‖) C := by
  refine smaller hg (fun _ => norm_nonneg _) (fun i => le_trans ?_ (P.loMass _ _ (he i).1))
  unfold Activities.regularOccurrence; rw [← h]
  by_cases hx : Healthy P.threshold (A.reg i).support U
  · rw [masked_eq _ _ _ _ hx, masked_eq _ _ _ _ hx]; exact (he i).2 U hx [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ hx, masked_ne _ _ _ _ hx,sub_zero,norm_zero]; exact (he i).1

lemma norm_bill {ι : Type*} {E : ι → ℝ} (C : ℝ) (h : SumBudget (fun i => ‖E i‖) C) : ‖∑' i, E i‖ ≤ C :=
  (norm_tsum_le_tsum_norm h.2.1).trans h.2.2

/-- Real cap-dependent fixed-volume estimate. Use `K_total` for this at
each x. Don't raise w using a uniform number of marked addresses. -/
lemma perturb {A B : Activities G n} (h : A.reg=B.reg) (h' : A.forced=B.forced) {C : ℝ} {p : ℕ → ℝ}
    (hc : SumBudget p C) (hb : ∀ i U, ‖A.K i U‖ ≤ p i) {ε : ℝ} (he : deviation P A B ε) (U : Config G n) :
    SumBudget (fun i => ‖A.regularOccurrence P i U-B.regularOccurrence P i U‖) ε ∧
    SumBudget (fun i => ‖A.gasOccurrence P i U-B.gasOccurrence P i U‖) (Real.exp C*(Real.exp ε-1)) := by
  obtain ⟨c,d,ha,ht,hg,hs⟩ := he
  exact ⟨masked_pay h ha hg U, gas_pay h' hc (smaller hs (fun i => (ht i).1) (fun i => P.loMass _ _ (ht i).1)) U
    (fun j => hb j U) (fun j => (ht j).2 U) P⟩

lemma rep_perturb {A B : Activities G n} {δ w δ' w' : ℝ} (hA : A.Valid P δ w) (hB : B.Valid P δ' w')
    (h : A.reg=B.reg) (h' : A.forced=B.forced) {C : ℝ} {p : ℕ → ℝ}
    (hc : SumBudget p C) (hb : ∀ i U, ‖A.K i U‖ ≤ p i) {ε : ℝ} (he : deviation P A B ε) (U : Config G n) :
    ‖A.additive P U-B.additive P U‖ ≤ ε ∧ ‖A.gas P U-B.gas P U‖ ≤ Real.exp C*(Real.exp ε-1) := by
  obtain ⟨hv,hh⟩ := perturb h h' hc hb he U
  have hw := norm_bill _ hv; have hx := norm_bill _ hh
  -- tsum over finsets, not a formal finite product symbol
  constructor
  · unfold Activities.additive; rw [← ((Activities.ESeries hA).summable U).tsum_sub
      ((Activities.ESeries hB).summable U)]; exact hw
  unfold Activities.gas; rw [← ((Activities.gasSeries hA).summable U).tsum_sub
    ((Activities.gasSeries hB).summable U)]; exact hx
end Payment
end YM.Progress.DirectedRecipe
