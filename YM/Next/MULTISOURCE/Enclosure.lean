import YM.Next.MULTISOURCE.Dealt
import YM.Next.MULTISOURCE.Larger

/-! Small radius unmarked stability pays the promised coefficient, including
      all volume-independent support reserves exactly at THIS vacuum. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Desk
open RG Wilson Lattice MeasureTheory Filter Finset MvPolynomial Reservoir Marker
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {I : Type} [Fintype I] [DecidableEq I] {G : Gauge} {n : Side}

omit [DecidableEq I] in
lemma permits (o : I → Site n) (k : I→ℝ) (ρ : ℝ) (he : ∀ i,0 ≤ k i) (ht : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ boxes r ⊆ allot o k ρ := by
  let m := 1+∑ i,k i
  have hp : 0<m := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ => he i)
  let r := ρ/m; have hr : 0<r := div_pos ht hp
  refine ⟨r,hr, fun z hz x => ?_⟩
  have hU : ∀ i : I, ‖z i‖ ≤ r := hz
  refine le_trans (b:=∑ i,r*k i) (sum_le_sum (fun i _ => ?_)) ?_
  · split
    · exact mul_le_mul_of_nonneg_right (hU i) (he i)
    exact mul_nonneg hr.le (he i)
  rw [← mul_sum]; exact (mul_le_mul_of_nonneg_left (show ∑ i,k i ≤ m from by unfold m; simp) hr.le).trans_eq
    (div_mul_cancel₀ _ hp.ne')

def feed (S : Finset I) (k : I→ℝ) (ρ ε : ℝ) := fun i => if i ∈ S then ρ/(k i+ε) else 0

lemma rewards (S : Finset I) (o : I → Site n) (k : I → ℝ) (ρ : ℝ) (ε : ℝ) (h : 0<ε) (ht : 0<ρ) (hk : ∀ i,0 ≤ k i)
    (hI : Set.InjOn o S) :
    let r := feed S k ρ ε
    (∀ i,0 ≤ r i) ∧ dome r ⊆ allot o k ρ ∧ 0 < price r (power S) ∧
      (price r (power S))⁻¹=ρ⁻¹^S.card*∏ i∈ S,(k i+ε) := by
  intro r
  have he i := add_pos_of_nonneg_of_pos (hk i) h
  have hr i (hi : i∈S) : r i=ρ/(k i+ε) := if_pos hi
  have hh i (hi : i ∉ S) : r i=0 := if_neg hi
  have hp i (hi : i∈S) : 0<r i := hr i hi ▸ div_pos ht (he i)
  refine ⟨fun i => by unfold r feed; split; exact (div_pos ht (he _)).le; exact le_rfl,?_,?_,?_⟩
  · intro z hz x
    have hl i : ‖z i‖ ≤ r i := hz i
    have hf i (hi : i∉S) : z i=0 := norm_le_zero_iff.mp ((hl i).trans_eq (hh i hi))
    change (∑ i, if o i=x then _ else (0:ℝ))≤ρ
    by_cases he : ∃ i∈S, o i=x
    · obtain ⟨i,hi,rfl⟩ := he
      rw [Finset.sum_eq_single i, if_pos rfl]; swap
      · intro b _ hb
        split
        · rename_i hi'
          rw [hf b (fun h => hb (hI h hi hi')),norm_zero,zero_mul]
        rfl
      · refine (mul_le_mul_of_nonneg_right (hl i) (hk i)).trans ((mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right h.le) (hp i hi).le).trans_eq ?_)
        rw [hr i hi,div_mul_cancel₀ _ (_root_.ne_of_gt (add_pos_of_nonneg_of_pos (hk i) h))]
      simp
    rw [Finset.sum_eq_zero ?_]; exact ht.le
    intro i _; split
    · rename_i hs; rw [hf i (fun h => he ⟨_,h,hs⟩),norm_zero,zero_mul]
    rfl
  · rw [reaches]; exact prod_pos hp
  rw [reaches,Finset.prod_congr rfl hr, ← prod_inv_distrib]
  simp only [mul_inv_rev,inv_inv,div_eq_mul_inv,prod_mul_distrib,prod_const]; ac_rfl

lemma passes_fee (o : I→Site n) (k : I → ℝ) (ρ C : ℝ) (hk : ∀ i,0≤k i) (ht : 0<ρ) (S : Finset I) (hI : Set.InjOn o S)
    (t : ℝ) (H : ∀ r : I→ℝ, (∀ i,0 ≤ r i) → dome r ⊆ allot o k ρ → 0 < price r (power S) → C ≤ t*(price r (power S))⁻¹) :
    C ≤ t * (ρ⁻¹^S.card * ∏ i∈ S, k i) := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (f:=fun _ : ℝ => C)
    (g:=fun s => t*(ρ⁻¹^S.card * ∏ i∈S,(k i+s))) (b:=𝓝[>] 0)
  · have ht : Continuous (fun s => t*(ρ⁻¹^S.card * ∏ i∈S,(k i+s))) := by fun_prop
    simpa using (ht.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨h1,h2,h3,h4⟩ := rewards S o k ρ ε hε ht hk hI
  rw [← h4]; exact H _ h1 h2 h3

variable {P : Rep G n} {κ : ℝ} (T : Reservoir P I) (o : I→Site n) (k : I→ℝ) (ρ : ℝ)
    (hk : ∀ i,0 ≤ k i) (hρ : 0 < ρ) (H : T.Tested κ (allot o k ρ))
include hk hρ H

lemma gained (S : Finset I) (hI : Set.InjOn o S) :
    let h := mints T (power S)
    let g := tolls T (power S)
    let b := ρ⁻¹^S.card*∏ i∈S,k i
    (∀ i, P.p.Regular (T.support i) (bite T (power S) i) ∧ h i∈taps P.p (T.support i) (bite T (power S) i)) ∧
      (∀ i, Legible P.p (T.k i) (chew T (power S) i) ∧ g i∈boxp (chew T (power S) i)) ∧
      (∀ x : Site n, SumBudget (fun i => if x ∈ T.support i then burn P.p 2 (T.support i)*h i else 0) b) ∧
      ∀ x : Site n,SumBudget (fun i => if x ∈ (T.k i).zone then burn P.p 2 (T.k i).zone*g i else 0) (κ*b) := by
  intro h g b
  obtain ⟨hx,hz,hB,-⟩ := rewards S o k ρ 1 zero_lt_one hρ hk hI
  have hm (i : ℕ) := (egress T H (power S) {i} _ hx hB hz).1 i (mem_singleton_self _)
  have hp (i : ℕ) := (vents T H (power S) {i} _ hx hB hz).1 i (mem_singleton_self _)
  refine ⟨hm, hp,?_,?_⟩ <;> intro x
  · let f i := if x∈ T.support i then burn P.p 2 (T.support i)*h i else 0
    have hf (i) : 0 ≤ f i := by unfold f; split; exact mul_nonneg (burn_pos ..).le (hm i).2.1; exact le_rfl
    have hl (Z : Finset ℕ) : ∑ i∈Z,f i ≤ b := by
      let C := ∑ i∈Z,f i
      have hh (q : I→ℝ) (Hq : ∀ i, 0≤q i) (hq : dome q ⊆ allot o k ρ) (hy : 0<price q (power S)) : C≤1*(price q (power S))⁻¹ := by
        rw [one_mul]; exact (egress T H (power S) Z q Hq hy hq).2 x
      have he := passes_fee o k _ C hk hρ S hI 1 hh; rw [one_mul] at he; exact he
    exact ⟨hf,summable_of_sum_le hf hl,Real.tsum_le_of_sum_le hf hl⟩
  let f i := if x∈ (T.k i).zone then burn P.p 2 (T.k i).zone*g i else 0
  have hf (i) : 0 ≤ f i := by unfold f; split; exact mul_nonneg (burn_pos ..).le (hp i).2.1; exact le_rfl
  have hh (Z : Finset ℕ) : ∑ i∈Z,f i ≤ κ*b :=
    passes_fee o k _ _ hk hρ S hI κ fun r hi hy hj => (vents T H (power S) Z _ hi hj hy).2 x
  exact ⟨hf,summable_of_sum_le hf hh,Real.tsum_le_of_sum_le hf hh⟩
end YM.Multi.Desk
