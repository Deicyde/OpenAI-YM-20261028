import YM.Push.ABSOLUTE_SUMS.Basic
import YM.Push.ABSOLUTE_SUMS.Packet

/-!
# One-seed price to full packet hit prices

`gain` denotes the exponential gain PER SEED (so typically `β * κ * t²`,
possibly with a fraction reserved for other uses). `spend` denotes an
exponential COST per seed (including e.g. other packet factors, variant
and trigger costs for which the producer has proved a per-packet bound).
Signs are opened. In addition, pay `a` for each B-ball of the complete
support. We give a sufficient inequality `fit` for a geometric tail
`totalCharge`. Post-L entropy constants; all independent of the period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Packets
open Lattice Wilson Pressure Pressure.Stores RG Finset Animals Lattice.Corona
open scoped BigOperators Classical
variable {c f : Side} (S : StepData c f)

def income (C spend gain : ℝ) (m : ℕ) := C * Real.exp ((spend-gain)*(m:ℝ))

def payment (B : ℕ) (a : ℝ) {c : Side} (s : Support c) := Real.exp (a*(coverNumber B s:ℝ))

def oneCost (l : ℕ) (a spend gain : ℝ) : ℝ := Real.exp (spend-gain+a*(seedCover l:ℝ))

def ratioCost (L : Side) (l B : ℕ) (a spend gain : ℝ) : ℝ :=
  ((stepCost L l B^2 : ℕ) : ℝ) * oneCost l a spend gain

/-- Named sufficient tree-vertex input (costs include mandatory packet
multiplicities; tree smallness will ask for a threshold also on
`totalCharge`). -/
def fit (L : Side) (l B : ℕ) (a spend gain q : ℝ) :=
  0 ≤ a ∧ ratioCost L l B a spend gain ≤ q ∧ q < 1

def totalCharge (L : Side) (C : ℝ) (l B : ℕ) (q : ℝ) (m : ℕ) : ℝ :=
  ((hitCost L l B:ℝ)*C) * q^(max 1 m) * (1-q)⁻¹



lemma cover_income (l B : ℕ) (A : Stores S) (h : connected S l B A) {C : ℝ}
    (hC : 0 ≤ C) (a spend gain : ℝ) (ha : 0 ≤ a) :
    income C spend gain A.shares * payment B a (dome A (l*B)) ≤
      C * oneCost l a spend gain ^ A.shares := by
  have he : coverNumber B (dome A (l*B)) ≤ A.shares*seedCover l := by
    rw [← support_reads S,← seeds_card S]; exact cover_support S _ _ _ h
  unfold income payment oneCost
  rw [mul_assoc,← Real.exp_add,← Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_monotone
  have hv : (coverNumber B (dome A (l*B)):ℝ) ≤ (A.shares:ℝ) * seedCover l := by exact_mod_cast he
  nlinarith only [mul_le_mul_of_nonneg_left hv ha]

def take (l B m : ℕ) (a : ℝ) (x : Site c) (w : Stores S → ℝ) (A : Stores S) : ℝ :=
  if connected S l B A ∧ x ∈ dome A (l*B) ∧ m ≤ A.shares then
    w A * payment B a (dome A (l*B)) else 0

lemma shares_nonzero (l B : ℕ) {A : Stores S} (h : connected S l B A) : 1 ≤ A.shares := by
  rw [← seeds_card S]
  exact Finset.card_pos.mpr h.1

/-- Hit by mandatory packets, including the tail and support weights.
Even if `w` has worse values where the address is not used.
A packet with zero seeds does **not** hit even when m=0. -/
lemma packet_income (l B : ℕ) (x : Site c) (w : Stores S → ℝ)
    {C a spend gain q : ℝ} (hC : 0 ≤ C)
    (hf : fit S.patch.L l B a spend gain q)
    (h : ∀ A : Stores S, connected S l B A → x ∈ dome A (l*B) →
      0 ≤ w A ∧ w A ≤ income C spend gain A.shares) (m : ℕ) :
    SumBudget (take S l B m a x w) (totalCharge S.patch.L C l B q m) := by
  let u := take S l B 0 a x w
  have he (A : Stores S) : 0 ≤ u A := by
    unfold u take
    split
    next he => exact mul_nonneg (h A he.1 he.2.1).1 (Real.exp_pos _).le
    next => exact le_rfl
  have hb (A : Stores S) : u A ≤ C * (oneCost l a spend gain)^A.shares := by
    unfold u take
    split
    next he =>
      exact (mul_le_mul_of_nonneg_right (h _ he.1 he.2.1).2 (Real.exp_pos _).le).trans
        (cover_income S l B _ he.1 hC _ _ _ hf.1)
    next => unfold oneCost; positivity
  have hv (k : ℕ) (s : Finset (Stores S))
      (H : ∀ A ∈ s, A.shares=k ∧ u A ≠ 0) : (s.card:ℝ) ≤ (hitCost S.patch.L l B:ℝ) *
        ((stepCost S.patch.L l B^2:ℕ):ℝ)^k := by
    have hh A (he : A∈s) := H A he
    have hi := stores_count S l B k x s (fun A hA => by
      obtain ⟨hg,hn⟩ := hh A hA
      refine ⟨hg,?_⟩
      unfold u take at hn
      split at hn
      next h => exact ⟨h.1,h.2.1⟩
      next => contradiction)
    exact_mod_cast hi
  have eq : take S l B m a x w = fun A => if max 1 m ≤ A.shares then u A else 0 := by
    funext A
    by_cases hc : connected S l B A
    · have hj := shares_nonzero S l B hc
      by_cases hm : m ≤ A.shares <;> simp [take,u,hc,hm,hj]
    simp [take,u,hc]
  rw [eq]
  exact budget_count_tail Stores.shares he hC (Nat.cast_nonneg (hitCost S.patch.L l B))
    (Nat.cast_nonneg (stepCost S.patch.L l B^2)) (Real.exp_pos _).le hb hv hf.2.1 hf.2.2 _

/-- FO-tree input shape. Choose `a` with space for any reserves. -/
lemma packet_hit (l B : ℕ) (w : Stores S → ℝ)
    {C a spend gain q : ℝ} (hC : 0 ≤ C)
    (hf : fit S.patch.L l B a spend gain q)
    (h : ∀ A : Stores S, connected S l B A → 0 ≤ w A ∧ w A ≤ income C spend gain A.shares) :
    Ac.Hit (fun A : Stores S => dome A (l*B)) B (fun A => if connected S l B A then w A else 0)
      a (totalCharge S.patch.L C l B q 0) := by
  intro x
  convert packet_income S l B x w hC hf (fun A hA _ => h A hA) 0 using 1
  ext A
  by_cases hc : connected S l B A <;> by_cases hx : x ∈ A.dome (l*B) <;>
    simp [take,payment,hc,hx]

/-- Can sum over COUNTABLY many variants, each with the actual packet
and physical footprint bound. The per-packet test still sees ALL variants;
this precedes any resummation into functions. For padding entries it is
convenient to allow arbitrary packet/footprint failures when price zero. -/
lemma packet_variants_tail {ι : Type*} (l B : ℕ) (x : Site c) (v : ι → Stores S)
    (X : ι → Support c) (w : ι → ℝ)
    {C a spend gain q : ℝ} (hC : 0 ≤ C) (hf : fit S.patch.L l B a spend gain q)
    (hg : ∀ i, 0 ≤ w i)
    (he : ∀ i, w i ≠ 0 → connected S l B (v i) ∧ X i ⊆ (v i).dome (l*B))
    (h : ∀ (A : Stores S), connected S l B A → ∀ s : Finset ι,
      (∀ i∈s, v i = A ∧ x ∈ X i) → ∑ i ∈ s, w i ≤ income C spend gain A.shares)
    (m : ℕ) :
    SumBudget
      (fun i => if x ∈ X i ∧ m ≤ (v i).shares then w i * payment B a (X i) else 0)
      (totalCharge S.patch.L C l B q m) := by
  let p := fun i => if x ∈ X i ∧ m ≤ (v i).shares then w i * payment B a (X i) else 0
  let b := fun A : Stores S => income C spend gain A.shares
  have hb A : 0 ≤ b A := by unfold b income; positivity
  have hp i : 0 ≤ p i := by
    unfold p; split
    · exact mul_nonneg (hg i) (Real.exp_pos _).le
    exact le_rfl
  refine budget_fiberwise v hp (fun k s hk => ?_) (packet_income S l B x b hC hf
    (fun A _ _ => ⟨hb A,le_rfl⟩) m)
  let t := s.filter (fun i => x ∈ X i ∧ m ≤ (v i).shares ∧ w i ≠ 0)
  have eq : ∑ i∈s, p i = ∑ i∈t, p i := (sum_subset (filter_subset ..) (by
    intro i hi hs'
    unfold p; split
    next hh =>
      have hz : w i = 0 := by by_contra hn; exact hs' (mem_filter.mpr ⟨hi, hh.1, hh.2, hn⟩)
      rw [hz, zero_mul]
    next => rfl)).symm
  change ∑ i ∈ s, p i ≤ take S l B m a x b k
  rw [eq]; rcases t.eq_empty_or_nonempty with ht|ht
  · rw [ht,sum_empty]; unfold take
    split
    next => exact mul_nonneg (hb k) (Real.exp_pos _).le
    next => exact le_rfl
  have hi i (hh : i∈t) : v i=k ∧ x∈X i ∧ m ≤ (v i).shares ∧ w i ≠0 :=
    ⟨hk _ (mem_filter.mp hh).1,(mem_filter.mp hh).2⟩
  obtain ⟨y,hy⟩ := ht
  obtain ⟨hz,hY,hH,hv⟩ := hi y hy
  obtain ⟨h1,h2⟩ := he y hv
  rw [hz] at h1 h2 hH
  unfold take; rw [if_pos ⟨h1,h2 hY,hH⟩]
  calc
    _ ≤ ∑ i∈t, w i * payment B a (dome k (l*B)) := sum_le_sum fun i hh => by
      obtain ⟨hy,hz,hv,hp⟩ := hi i hh
      unfold p; rw [if_pos ⟨hz,hv⟩]
      have hh := (he i hp).2; rw [hy] at hh
      apply mul_le_mul_of_nonneg_left _ (hg i)
      exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast cover_mono hh B) hf.1)
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (h k h1 t fun i h => ⟨(hi i h).1,(hi i h).2.1⟩)
        (Real.exp_pos _).le

lemma packet_variants {ι : Type*} (l B : ℕ) (v : ι → Stores S) (X : ι → Support c) (w : ι → ℝ)
    {C a spend gain q : ℝ} (hC : 0 ≤ C) (hf : fit S.patch.L l B a spend gain q)
    (hg : ∀ i, 0 ≤ w i)
    (he : ∀ i, w i ≠ 0 → connected S l B (v i) ∧ X i ⊆ (v i).dome (l*B))
    (h : ∀ (A : Stores S), connected S l B A → ∀ s : Finset ι,
      (∀ i∈s, v i = A) → ∑ i ∈ s, w i ≤ income C spend gain A.shares) :
    Ac.Hit X B w a (totalCharge S.patch.L C l B q 0) := by
  intro x
  simpa [payment] using packet_variants_tail S l B x v X w hC hf hg he
    (fun A hA s H => h A hA s fun i hi => (H i hi).1) 0
end YM.Push.AbsoluteSums.Packets
