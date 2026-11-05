import YM.Ac.Table
import YM.Corona.Halo
import YM.RG.Activities
/-! FHtree distinct-address production including full cover exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Ac
open Relation Lattice Corona Finset RG
open scoped Classical
variable {ι : Type*} [DecidableEq ι] {n : Side} (X : ι → Support n) (M : ℕ)

def Hit (f : ι → ℝ) (a γ : ℝ) := ∀ x : Site n,
    SumBudget (fun i => if x∈X i then f i * Real.exp (a*coverNumber M (X i)) else 0) γ

omit [DecidableEq ι] in
lemma demand {f : ι → ℝ} {a γ} (hh : Hit X M f a γ)
    (Y : Support n) (D : Finset ι) : ∑ i∈buds X D Y,f i*Real.exp (a*coverNumber M (X i)) ≤ Y.card*γ := by
  let w := fun i => f i*Real.exp (a*coverNumber M (X i))
  let p := fun x i => if x∈ X i then w i else 0
  calc
    _ ≤ ∑ i∈buds X D Y, ∑ x∈Y,p x i := by
      apply sum_le_sum; intro i hi; obtain ⟨x,h1,h2⟩ := ((alive X D Y).mp hi).2
      apply le_trans _ (single_le_sum (f:=fun k => p k i) (fun x _ => (hh x).1 i) h1)
      simp [p,w,h2]
    _ ≤ Y.card*γ := by
      rw [sum_comm]; apply le_trans _ (le_of_eq (show ∑ _ ∈ Y, γ = _ by simp)); apply sum_le_sum; intro x _
      exact ((hh x).2.1.sum_le_tsum (buds X D Y) (fun i _ => (hh x).1 i)).trans (hh x).2.2

private lemma step {f : ι → ℝ} {a γ} (hf : ∀ i, 0 ≤ f i) (hh : Hit X M f (a+1) γ)
    (D : Finset ι) (Y : Support n) (H : ∀ P, P ⊂ D → ∀ y,
      film X P y (fun i => f i * Real.exp (a*coverNumber M (X i))) ≤ Real.exp (coverNumber M y)) :
      film X D Y (fun i => f i * Real.exp (a*coverNumber M (X i))) ≤ Real.exp (Y.card*γ) := by
  let p := fun i => f i * Real.exp (a*coverNumber M (X i))
  let g := fun i => f i * Real.exp ((a+1)*coverNumber M (X i))
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
        simp only [p,g, add_mul, one_mul, Real.exp_add,mul_assoc]))
    _ ≤ _ := by rw [← Real.exp_sum, Real.exp_le_exp]; exact demand X M hh Y D

private lemma all_pack {f : ι → ℝ} {a γ} (hf : ∀ i, 0 ≤ f i) (hh : Hit X M f (a+1) γ) (hp : (M+M+1:ℕ)^4*(γ:ℝ) ≤ 1)
    (hG : 0≤γ) (D : Finset ι) (Y : Support n) :
      film X D Y (fun i => f i * Real.exp (a*coverNumber M (X i))) ≤ Real.exp (coverNumber M Y) := by
  induction D using Finset.strongInduction generalizing Y with
  | H s hs =>
    apply (step X M hf hh s Y hs).trans
    rw [Real.exp_le_exp]
    have hy : (Y.card:ℝ) ≤ coverNumber M Y*((M+M+1:ℕ):ℝ)^4 := by exact_mod_cast pays Y M
    have H1 := mul_le_mul_of_nonneg_left hp (show (0:ℝ) ≤ coverNumber M Y by positivity)
    exact (mul_le_mul_of_nonneg_right hy hG).trans (by nlinarith only [H1])

lemma cover {s : Finset ι} (hs : Spark X s) : coverNumber M (s.biUnion X) ≤ ∑ i∈s,coverNumber M (X i) := by
  classical
  have h : ∀ k : ℕ, k+1≤ s.card → ∃ u⊆s,u.card=k+1 ∧ coverNumber M (u.biUnion X) ≤ ∑ i∈u,coverNumber M (X i) := by
    intro k; induction k with
    | zero =>
      intro _; obtain ⟨i,hi⟩ := hs.1; exact ⟨{i},by simp [hi],by simp,by simp⟩
    | succ k IH =>
      intro hh
      obtain ⟨u,h1,h2,h3⟩ := IH (by omega)
      obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<u.card by omega); obtain ⟨j,hj,hx⟩ := exists_mem_notMem_of_card_lt_card (show u.card<s.card by omega)
      have H : ∀ j, chain X s i j → j∉u → ∃ t∈s,t∉u ∧ meets X t (u.biUnion X) := by
        intro b hb; induction hb with
        | refl => exact fun H => absurd hi H
        | @tail a b _ ht I =>
          intro h; by_cases hn : a∈u
          · obtain ⟨q,hq,hp⟩ := ht.2.2; exact ⟨b,ht.2.1,h,q,mem_biUnion.mpr ⟨a,hn,hq⟩,hp⟩
          exact I hn
      obtain ⟨t,ht,hz,x,hp,hq⟩ := H j (hs.2 i (h1 hi) j hj) hx
      refine ⟨insert t u,insert_subset ht h1,by simp only [card_insert_of_notMem hz,h2],?_⟩
      rw [sum_insert hz,biUnion_insert]
      exact (meets_sum hq hp M).trans (Nat.add_le_add_left h3 _)
  obtain ⟨a,ha⟩ := Nat.exists_eq_add_one.mpr (Finset.card_pos.mpr hs.1)
  obtain ⟨u,h1,h2,h3⟩ := h a ha.ge
  rwa [Finset.eq_of_subset_of_card_le h1 (ha ▸ h2.ge)] at h3

def roots (f : ι → ℝ) (a : ℝ) (x : Site n) := fun s : Finset ι => if Spark X s ∧ x∈s.biUnion X then
    Real.exp (a*coverNumber M (s.biUnion X)) * ∏ i∈s,f i else 0

/-- NONrepeating tree hit sums: actual Countably many labels, includes native cover price.
Marking lemma etc separate. -/
lemma forest {f : ι → ℝ} {a γ} (ha : 0≤ a) (hf : ∀ i, 0 ≤ f i) (hh : Hit X M f (a+1) γ)
    (hp : (M+M+1:ℕ)^4*(γ:ℝ) ≤ 1) (hG : 0≤γ) (x : Site n) :
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
    have hU := step X M hf hh A Y fun P _ y => all_pack X M hf hh hp hG P y
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
