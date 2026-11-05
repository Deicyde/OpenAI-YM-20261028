import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2

/-! Quantitative continuity costs on **one** census. In the gas comparison
pay for all subsets of forced labels. No derivative in U or changes of masks in
that comparison. No volume-independent bound claimed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Lattice Wilson RG RG.Activities RG.Shoot MeasureTheory Filter Finset Function
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff

lemma budget_unweighted {ι : Type*} {P : BudgetPoint} {n : Side} {X : ι → Support n} {b : ι → ℝ}
    {δ : ℝ} (hn : ∀ i, 0 ≤ b i) (hB : SumBudget (fun i => P.mass (X i) (b i)) δ) : SumBudget b δ := by
  have he i := P.loMass (X i) (b i) (hn i)
  have hs := hB.2.1.of_nonneg_of_le hn he
  exact ⟨hn,hs,(hs.tsum_le_tsum he hB.2.1).trans hB.2.2⟩

lemma summable_mass {ι : Type*} {n : Side} (P : BudgetPoint) (X : ι → Support n) {b : ι → ℝ}
    (hn : ∀ i, 0 ≤ b i) (hs : Summable b) : Summable fun i => P.mass (X i) (b i) := by
  have he (i) := (coverNumber_realized P.B (X i)).choose_spec.2.symm.le.trans
    ((coverNumber_realized P.B (X i)).choose.card_le_univ)
  apply (hs.mul_left (Real.exp (P.supportExponent * (Fintype.card (Site n):ℝ)))).of_nonneg_of_le
  · intro i; exact mul_nonneg (Real.exp_pos _).le (hn i)
  intro i; unfold BudgetPoint.mass; gcongr
  · exact hn _
  · exact P.exponent_pos.le
  exact he i

lemma exponential_sum {ι : Type*} {v : ι → ℝ} (h0 : ∀ i, 0 ≤ v i) (hv : Summable v) :
    (∑' b : Finset ι, ∏ i ∈ b, v i) ≤ Real.exp (∑' i, v i) := by
  classical
  refine (summable_finsetProd_of_summable_nonneg h0 hv).tsum_le_of_sum_le fun s => ?_
  calc
    _ ≤ ∑ b ∈ (s.biUnion id).powerset, ∏ i ∈ b, v i := sum_le_sum_of_subset_of_nonneg
      (fun i hi => mem_powerset.mpr (subset_biUnion_of_mem id hi)) (fun _ _ _ => prod_nonneg fun i _ => h0 i)
    _ = ∏ i ∈ s.biUnion id, (1 + v i) := (prod_one_add _).symm
    _ ≤ Real.exp (∑' i, v i) := (Real.prod_one_add_le_exp_sum _ h0).trans
      (Real.exp_monotone (hv.sum_le_tsum _ (fun i _ => h0 i)))

lemma product_diff {ι : Type*} {δ : ℝ} (hδ : 0 ≤ δ) (p q h : ι → ℝ) (hp : ∀ i, ‖p i‖ ≤ h i)
    (hq : ∀ i, ‖q i‖ ≤ h i) (he : ∀ i, ‖p i-q i‖ ≤ δ*h i) (b : Finset ι) :
    ‖(∏ i ∈ b, p i) - (∏ i ∈ b, q i)‖ ≤ δ * ∏ i ∈ b, (2*h i) := by
  classical
  induction b using Finset.induction_on with
  | empty => simpa using hδ
  | @insert i b hi ih =>
    let w := ∏ j ∈ b, (2*h j)
    have h0 (i) := (norm_nonneg _).trans (hp i)
    have hq' : ‖∏ j ∈ b, q j‖ ≤ w := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        fun j _ => (hq j).trans (by linarith [h0 j])
    rw [prod_insert hi, prod_insert hi, prod_insert hi]
    calc
      _ ≤ ‖(p i-q i)*(∏ j ∈ b, q j)‖ + ‖p i * ((∏ j ∈ b, p j)-(∏ j ∈ b, q j))‖ := by
        rw [show p i * _ - q i * _ = (p i-q i)*(∏ j ∈ b, q j) + p i*((∏ j ∈ b, p j)-(∏ j ∈ b, q j)) by ring]
        exact norm_add_le ..
      _ ≤ (δ*h i)*w + h i*(δ*w) := by
        rw [norm_mul,norm_mul]; exact add_le_add
          (mul_le_mul (he i) hq' (norm_nonneg _) (mul_nonneg hδ (h0 i)))
          (mul_le_mul (hp i) ih (norm_nonneg _) (h0 i))
      _ = _ := by unfold w; ring

variable {n : Side} {G : Gauge} {P : BudgetPoint} {S T : Activities G n}

lemma gas_diff {d k : ℕ → ℝ} (h : S.forced = T.forced) {δ : ℝ} (hd : SumBudget d δ) (hδ : 0 < δ) (h1 : δ ≤ 1)
    (he : ∀ i x, ‖S.K i x-T.K i x‖ ≤ d i) (hh : ∀ i x, ‖S.K i x‖ ≤ k i) (hk : Summable k) (x : Config G n) :
    ‖S.gas P x - T.gas P x‖ ≤ δ * Real.exp (2*((∑' i, k i)+1)) := by
  classical
  let v (i) := k i + δ⁻¹*d i
  have hS (i) := hh i x
  have h₁ i : k i ≤ v i := le_add_of_nonneg_right (mul_nonneg (inv_pos.mpr hδ).le (hd.1 i))
  have h₂ i : d i ≤ δ*v i := by
    unfold v; rw [mul_add,mul_inv_cancel_left₀ hδ.ne']; exact le_add_of_nonneg_left
      (mul_nonneg hδ.le ((norm_nonneg _).trans (hS i)))
  have hp i := (hS i).trans (h₁ i)
  have h0 i := (norm_nonneg _).trans (hp i)
  have hT i : ‖T.K i x‖ ≤ v i := by
    have ha := norm_sub_le (S.K i x) (S.K i x-T.K i x)
    rw [sub_sub_cancel] at ha
    exact ha.trans (add_le_add (hS i) ((he i x).trans (le_mul_of_one_le_left (hd.1 i)
      (one_le_inv₀ hδ |>.mpr h1))))
  have hs : Summable v := hk.add (hd.2.1.mul_left _)
  have htotal : (∑' i, 2*v i) ≤ 2*((∑' i, k i)+1) := by
    unfold v; rw [tsum_mul_left,hk.tsum_add (hd.2.1.mul_left _),tsum_mul_left]; gcongr
    exact (mul_le_mul_of_nonneg_left hd.2.2 (inv_pos.mpr hδ).le).trans_eq (inv_mul_cancel₀ hδ.ne')
  have adm (b : Finset ℕ) : S.admissible P x b = T.admissible P x b := by simp only [admissible,h]
  have ha := summable_finsetProd_of_summable_nonneg h0 hs
  have ht (M : Activities G n) (h : ∀ i, ‖M.K i x‖ ≤ v i) : Summable fun b => M.gasOccurrence P b x :=
    .of_norm_bounded ha fun b => by
      unfold gasOccurrence; split
      · rw [norm_prod]; exact prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => h i)
      · rw [norm_zero]; exact prod_nonneg fun i _ => h0 i
  have h0' i : 0 ≤ 2*v i := mul_nonneg zero_le_two (h0 i)
  have ha' := (summable_finsetProd_of_summable_nonneg h0' (hs.mul_left 2)).mul_left δ
  have he' b : ‖S.gasOccurrence P b x-T.gasOccurrence P b x‖ ≤ δ * ∏ i ∈ b, (2*v i) := by
    unfold gasOccurrence; rw [adm]; split
    · exact product_diff hδ.le _ _ _ hp hT (fun i => (he i x).trans (h₂ i)) b
    · simp only [sub_zero,norm_zero]; exact mul_nonneg hδ.le (prod_nonneg fun i _ => h0' i)
  have hb := ha'.of_nonneg_of_le (fun _ => norm_nonneg _) he'
  rw [gas,gas,← (ht S hp).tsum_sub (ht T hT)]
  refine (norm_tsum_le_tsum_norm hb).trans ((hb.tsum_le_tsum he' ha').trans ?_)
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left
    ((exponential_sum h0' (hs.mul_left 2)).trans (Real.exp_le_exp.mpr htotal)) hδ.le

lemma additive_diff {δ δ₁ δ₂ w₁ w₂ : ℝ} (hS : S.Valid P δ₁ w₁) (hT : T.Valid P δ₂ w₂)
    (h : S.reg = T.reg) {b : ℕ → ℝ} (hb : SumBudget b δ)
    (hh : ∀ i, variesRegular P (S.reg i) (S.E i) (T.E i) (b i)) (x : Config G n) : ‖S.additive P x-T.additive P x‖ ≤ δ := by
  have he (i) : ‖S.regularOccurrence P i x-T.regularOccurrence P i x‖ ≤ b i := by
    unfold regularOccurrence; rw [← h]; by_cases hv : Healthy P.threshold (S.reg i).support x
    · rw [masked_eq _ _ _ _ hv,masked_eq _ _ _ _ hv]; exact (hh i).2 _ hv [] (Nat.zero_le _) (by simp)
    · rw [masked_ne _ _ _ _ hv,masked_ne _ _ _ _ hv,sub_zero,norm_zero]; exact hb.1 i
  have hs := hb.2.1.of_nonneg_of_le (fun _ => norm_nonneg _) he
  rw [additive, additive,← ((ESeries hS).summable x).tsum_sub ((ESeries hT).summable x)]
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum he hb.2.1).trans hb.2.2)

lemma deviation_diff {δ δ₁ δ₂ w₁ w₂ : ℝ} (hS : S.Valid P δ₁ w₁) (hT : T.Valid P δ₂ w₂)
    {k : ℕ → ℝ} (hh : ∀ i x, ‖S.K i x‖ ≤ k i) (hk : Summable k)
    (hreg : S.reg = T.reg) (hf : S.forced = T.forced) (hd : deviation P S T δ) (h0 : 0 < δ) (h1 : δ ≤ 1)
    (x : Config G n) : ‖S.additive P x - T.additive P x‖ ≤ δ ∧ ‖S.gas P x - T.gas P x‖ ≤ δ * Real.exp (2*((∑' i, k i)+1)) := by
  obtain ⟨c,d,hc,hd,hC,hD⟩ := hd
  exact ⟨additive_diff hS hT hreg (budget_unweighted (fun i => (hc i).1) hC) hc x,
    gas_diff hf (budget_unweighted (fun i => (hd i).1) hD) h0 h1 (fun i => (hd i).2) hh hk x⟩
end YM.Push.BetaTransport
