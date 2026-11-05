import YM.Corona.Halo
import YM.Extra.SOURCE_HISTORIES.Clusters

/-! Summability and price of K families meeting the birth stencil at the
**actual vacuum support exponent**, incl genuine winding costs. No volume
powers; no differentiation of predicates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Attach
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {n : Side} {G : Gauge} (R : Rep G n) (Y : Support n)

lemma lengths (k : ℕ) (b : Finset ℕ) (h : ∀ i ∈ b, ¬Disjoint (X R i) Y) :
    coverNumber k (Y∪b.biUnion (X R)) ≤ coverNumber k Y + ∑ i ∈ b, coverNumber k (X R i) := by
  classical
  induction b using Finset.induction_on with
  | empty => simp
  | @insert i b hi ih =>
    obtain ⟨x,hx,hb⟩ := Finset.not_disjoint_iff.mp (h i (by simp))
    rw [Finset.sum_insert hi,Finset.biUnion_insert]
    rw [show Y ∪ (X R i ∪ b.biUnion (X R))=X R i∪(Y∪b.biUnion (X R)) by rw [Finset.union_left_comm]]
    refine le_trans (Corona.meets_sum hx (Finset.mem_union_left _ hb) k) ?_
    specialize ih fun i hi => h i (by simp [hi])
    omega

private lemma tab (c : Cluster R Y) (f : ℕ → ℝ) (h : ∀ i, 0 ≤ f i) :
    R.p.mass (span R Y c) (∏ i ∈ c.val, f i) ≤ R.p.mass Y 1 * ∏ i ∈ c.val, R.p.mass (X R i) (f i) := by
  let x := R.p.B
  let A := R.p.supportExponent
  have he : A * (coverNumber x (span R Y c) : ℝ) ≤ A * coverNumber x Y + ∑ i ∈ c.val, A * coverNumber x (X R i) := by
    rw [← Finset.mul_sum,← mul_add]
    apply mul_le_mul_of_nonneg_left _ R.p.exponent_pos.le
    exact_mod_cast lengths R Y x c.val c.property.2.2
  unfold BudgetPoint.mass
  rw [Finset.prod_mul_distrib]
  refine (mul_le_mul_of_nonneg_right (Real.exp_monotone he) (Finset.prod_nonneg (fun i _ => h i))).trans_eq ?_
  rw [Real.exp_add,Real.exp_sum,mul_one,mul_assoc]

private lemma hit_all {f : ℕ → ℝ} {w : ℝ}
    (hp : ∀ x : Site n, SumBudget (fun i => if x∈X R i then f i else 0) w)
    (D : Finset ℕ) (he : ∀ i ∈ D, ¬Disjoint (X R i) Y) : ∑ i ∈ D, f i ≤ Y.card*w := by
  classical
  let g (x : Site n) (i : ℕ) := if x∈X R i then f i else 0
  have ht (i) (hi : i∈D) : f i ≤ ∑ x ∈ Y, g x i := by
    obtain ⟨x,hx,hh⟩ := Finset.not_disjoint_iff.mp (he _ hi)
    rw [show f i = g x i from (if_pos hx).symm]
    exact Finset.single_le_sum (f:=fun v => g v i) (fun y _ => (hp y).1 i) hh
  calc
    _ ≤ ∑ i ∈ D, ∑ x ∈ Y, g x i := Finset.sum_le_sum ht
    _ = ∑ x ∈ Y, ∑ i ∈ D, g x i := Finset.sum_comm
    _ ≤ ∑ _ ∈ Y, w := Finset.sum_le_sum fun i _ => le_trans ((hp i).2.1.sum_le_tsum _
      (fun k _ => (hp i).1 k)) ((hp i).2.2)
    _ = _ := by simp

lemma budget_cluster {f : ℕ → ℝ} (h : ∀ i, 0 ≤ f i) {w : ℝ}
    (hw : ∀ x : Site n, SumBudget (fun i => if x ∈ X R i then R.p.mass (X R i) (f i) else 0) w) :
    SumBudget (fun c : Cluster R Y => R.p.mass (span R Y c) (∏ i∈c.val, f i))
      (R.p.mass Y 1 * (Real.exp (Y.card*w)-1)) := by
  classical
  let a i := R.p.mass (X R i) (f i)
  have ha i : 0 ≤ a i := mul_nonneg (Real.exp_pos _).le (h i)
  have hA : 0 ≤ R.p.mass Y 1 := mul_nonneg (Real.exp_pos _).le zero_le_one
  let g (b : Finset ℕ) := ∏ i ∈ b, a i
  have hg (b) : 0 ≤ g b := Finset.prod_nonneg (fun i _ => ha i)
  let L (c : Cluster R Y) := R.p.mass (span R Y c) (∏ i∈c.val, f i)
  have hl (c) : 0 ≤ L c := mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ => h i))
  have he (s : Finset (Cluster R Y)) :
      ∑ c ∈ s, L c ≤ R.p.mass Y 1 * (Real.exp (Y.card*w)-1) := by
    let D := s.biUnion Subtype.val
    have ht (i) (hi : i∈D) : ¬Disjoint (X R i) Y := by
      obtain ⟨j,-,hh⟩ := Finset.mem_biUnion.mp hi; exact j.property.2.2 i hh
    have hy : ∏ i∈D, (a i + 1) ≤ Real.exp (Y.card*w) := calc
      _ ≤ ∏ i∈D, Real.exp (a i) := Finset.prod_le_prod (fun i _ => by specialize ha i; linarith)
        (fun i _ => Real.add_one_le_exp _)
      _ = Real.exp (∑ i ∈ D, a i) := (Real.exp_sum ..).symm
      _ ≤ _ := Real.exp_monotone (hit_all R Y hw D ht)
    have hx : s.image Subtype.val ⊆ D.powerset.erase ∅ := by
      intro c hc
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_erase.mpr ⟨b.property.1.ne_empty, Finset.mem_powerset.mpr
        (fun _ hk => Finset.mem_biUnion.mpr ⟨_,hb,hk⟩)⟩
    have hu : ∑ b ∈ D.powerset.erase ∅, g b = ∏ i∈D, (a i + 1) - 1 := by
      have hs : ∏ i∈D, (a i + 1) = ∑ b ∈ D.powerset,g b := by simpa [g] using Finset.prod_add a (fun _ => 1) D
      rw [eq_sub_iff_add_eq,hs,← Finset.sum_erase_add _ _ (show ∅∈D.powerset by simp)]
      rw [show g ∅ = 1 from Finset.prod_empty]
    calc
      _ ≤ ∑ c ∈ s, R.p.mass Y 1 * g c.val := Finset.sum_le_sum (fun c _ => tab R Y c f h)
      _ = R.p.mass Y 1 * ∑ b ∈ s.image Subtype.val,g b := by
        rw [Finset.sum_image Subtype.val_injective.injOn, Finset.mul_sum]
      _ ≤ R.p.mass Y 1 * ∑ b ∈ D.powerset.erase ∅,g b := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hx (fun i _ _ => hg i)) hA
      _ ≤ _ := by rw [hu]; exact mul_le_mul_of_nonneg_left (sub_le_sub_right hy _) hA
  exact ⟨hl, summable_of_sum_le hl he, Real.tsum_le_of_sum_le hl he⟩

end YM.Extra.Histories.Attach
