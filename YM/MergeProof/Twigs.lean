import YM.Ac.Tree
/-! FHtree distinct-address production including full cover exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Ac
open Relation Lattice Corona Finset RG
open scoped Classical
variable {ι : Type*} [DecidableEq ι] {n : Side} (X : ι → Support n) (M : ℕ)

private lemma stepP {f : ι → ℝ} {a γ w : ℝ} (hf : ∀ i, 0 ≤ f i) (hh : Hit X M f (a+w) γ)
    (D : Finset ι) (Y : Support n) (H : ∀ P, P ⊂ D → ∀ y,
      film X P y (fun i => f i * Real.exp (a*coverNumber M (X i))) ≤ Real.exp (w*coverNumber M y)) :
      film X D Y (fun i => f i * Real.exp (a*coverNumber M (X i))) ≤ Real.exp (Y.card*γ) := by
  let p := fun i => f i * Real.exp (a*coverNumber M (X i))
  let g := fun i => f i * Real.exp ((a+w)*coverNumber M (X i))
  have hy (i) : 0≤p i := mul_nonneg (hf _) (Real.exp_pos _).le
  apply (lookup X D Y p hy).trans
  calc
    _ ≤ ∏ i∈buds X D Y, Real.exp (g i) := by
      apply prod_le_prod
      · intro i _; unfold film; exact add_nonneg zero_le_one (mul_nonneg (hy i) (sum_nonneg fun s _ => prod_nonneg fun j _ => hy j))
      intro i hi
      apply le_trans _ (Real.add_one_le_exp _)
      rw [add_comm]; gcongr
      exact (mul_le_mul_of_nonneg_left (H _ (erase_ssubset ((alive X D Y).mp hi).1) (X i)) (hy i)).trans (le_of_eq (by
        simp only [p,g, add_mul, Real.exp_add,mul_assoc]))
    _ ≤ _ := by rw [← Real.exp_sum, Real.exp_le_exp]; exact demand X M hh Y D

private lemma all_price {f : ι → ℝ} {a γ w : ℝ} (hf : ∀ i, 0 ≤ f i) (hh : Hit X M f (a+w) γ) (hp : (M+M+1:ℕ)^4*(γ:ℝ) ≤ w)
    (hG : 0≤γ) (D : Finset ι) (Y : Support n) :
      film X D Y (fun i => f i * Real.exp (a*coverNumber M (X i))) ≤ Real.exp (w*coverNumber M Y) := by
  induction D using Finset.strongInduction generalizing Y with
  | H s hs =>
    apply (stepP X M hf hh s Y hs).trans
    rw [Real.exp_le_exp]
    have hy : (Y.card:ℝ) ≤ coverNumber M Y*((M+M+1:ℕ):ℝ)^4 := by exact_mod_cast pays Y M
    have H1 := mul_le_mul_of_nonneg_left hp (show (0:ℝ) ≤ coverNumber M Y by positivity)
    exact (mul_le_mul_of_nonneg_right hy hG).trans (by nlinarith only [H1])

lemma forest_price {f : ι → ℝ} {a γ w : ℝ} (ha : 0≤ a) (hf : ∀ i, 0 ≤ f i) (hh : Hit X M f (a+w) γ)
    (hp : (M+M+1:ℕ)^4*(γ:ℝ) ≤ w) (hG : 0≤γ) (x : Site n) :
    SumBudget (roots X M f a x) (Real.exp γ-1) := by
  have he (i : Finset ι) : 0≤roots X M f a x i := by
    unfold roots; split
    · exact mul_nonneg (Real.exp_pos _).le (prod_nonneg fun i _ => hf i)
    exact le_rfl
  let Y := ({x} : Support n)
  have hy (s : Finset (Finset ι)) : (∑ i∈s,roots X M f a x i) ≤ Real.exp γ-1 := by
    let A := s.biUnion id
    let F := (pouch X A Y)
    let v := fun i => f i * Real.exp (a*coverNumber M (X i))
    let g := fun p : Finset ι => ∏ i∈p,v i
    let u := s.filter (fun p => Spark X p ∧ x∈p.biUnion X)
    have hU := stepP X M hf hh A Y fun P _ y => all_price X M hf hh hp hG P y
    have hC : ∑ p∈F.erase ∅,g p ≤ Real.exp γ-1 := by
      have hs : (∅:Finset ι) ∈ F := (op _ _ _).mpr ⟨empty_subset _,fun _ hi => absurd hi (notMem_empty _)⟩
      rw [le_sub_iff_add_le, show (1:ℝ) = g ∅ by simp [g], sum_erase_add F _ hs]
      simpa only [F, g,v,film,Y, card_singleton, Nat.cast_one, one_mul] using hU
    calc
      _ = ∑ i ∈ u,roots X M f a x i := by
        symm; apply sum_subset (filter_subset ..)
        intro s hs hh'; have hj : ¬ (Spark X s ∧ x∈s.biUnion X) := fun H => hh' (mem_filter.mpr ⟨hs,H⟩)
        exact if_neg hj
      _ ≤ ∑ i ∈ u, g i := by
        refine sum_le_sum fun i hi => ?_
        have h := (mem_filter.mp hi).2
        unfold roots; rw [if_pos h]; simp only [g,v,prod_mul_distrib,← Real.exp_sum,← mul_sum]
        rw [mul_comm]; gcongr
        · exact prod_nonneg fun i _ => hf i
        exact_mod_cast cover X M h.1
      _ ≤ _ := by
        apply le_trans _ hC; apply sum_le_sum_of_subset_of_nonneg
        · intro j hj; obtain ⟨hj',hr,hp⟩ := mem_filter.mp hj; obtain ⟨b,h1,h2⟩ := mem_biUnion.mp hp
          refine mem_erase.mpr ⟨hr.1.ne_empty,(op _ _ _).mpr ⟨fun k hk => mem_biUnion.mpr ⟨j,hj',hk⟩,?_⟩⟩
          exact fun i hi => ⟨b,h1,⟨x,mem_singleton_self _,h2⟩,hr.2 b h1 i hi⟩
        intro i _ _; exact prod_nonneg fun j _ => (mul_nonneg (hf j) (Real.exp_pos _).le)
  have ht := summable_of_sum_le (f:=roots X M f a x) he hy
  exact ⟨he,ht,ht.tsum_le_of_sum_le hy⟩
end YM.Ac
