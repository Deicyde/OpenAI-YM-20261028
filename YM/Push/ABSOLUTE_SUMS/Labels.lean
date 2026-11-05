import YM.Overlay.Engine
import YM.Push.ABSOLUTE_SUMS.Footprint
import YM.Slice.Gate

/-!
# Support tests consuming actual family bounds

Typed input `A` still on the fine fields; the footprint prices here
are upper bounds for propagation subject to the stated per-label
costs and footprint dominance. If using a different branch, masked
E formula, anchors or witnesses with several variants etc, check the
tests ANEW. No assertion on applicability of the `E_i` seminorm to a
new expression (domain/analytic question) from the footprint alone.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Labels
open Lattice RG Wilson Finset Footprint
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {c f : Side} {ι κ : Type*}

-- General hit estimate manipulation

def unitPrice (X : ι → Support c) (B : ℕ) (w : ι → ℝ) (a : ℝ) (x : Site c) (i : ι) :=
    if x ∈ X i then w i * Real.exp (a*coverNumber B (X i)) else 0

lemma anchor_weaker (X : ι → Support c) (M : ℕ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {A γ : ℝ} (h : Ac.Hit X M w A γ) (p : ι → Site c) (he : ∀ i, p i ∈ X i) :
    Footprint.Anchored p w (fun i => coverNumber M (X i)) A γ := by
  intro x; refine budget_mono (h x) (fun i => ?_) fun i => ?_
  · split <;> first | exact mul_nonneg (hw _) (Real.exp_pos _).le | exact le_rfl
  split
  next hn => rw [if_pos (hn ▸ he _)]
  next hn => exact (h x).1 i

lemma raise_prices (X : ι → Support c) (M : ℕ) {w u : ι → ℝ} (hu : ∀ i, 0 ≤ u i)
    {A γ : ℝ} (h : Ac.Hit X M w A γ) (he : ∀ i, u i ≤ w i) : Ac.Hit X M u A γ := by
  intro x
  apply budget_mono (h x)
  · intro i; split <;> first | exact mul_nonneg (hu _) (Real.exp_pos _).le | exact le_rfl
  intro i; split <;> first | exact mul_le_mul_of_nonneg_right (he _) (Real.exp_pos _).le | exact le_rfl

/-- `X` can be an OVER-paying footprint; Y actual. `p` maps all
variants to the common parent, summing their costs before pricing that
footprint. No assumption labels with blank Plots can be removed from
a parent address without keeping history; this only drops zeros in a
bound. -/
lemma variants (X : ι → Support c) (M : ℕ) {w : ι → ℝ}
    {A γ : ℝ} (ha : 0 ≤ A) (h : Ac.Hit X M w A γ) (Y : κ → Support c) (p : κ → ι)
    (g : κ → ℝ) (hg : ∀ i, 0 ≤ g i) (he : ∀ i, g i ≠ 0 → Y i ⊆ X (p i))
    (hv : ∀ i (s : Finset κ), (∀ j∈s, p j=i) → ∑ j∈s, g j ≤ w i) : Ac.Hit Y M g A γ := by
  intro x
  let f := unitPrice Y M g A x
  have hf i : 0 ≤ f i := by
    unfold f unitPrice; split <;> first | exact mul_nonneg (hg _) (Real.exp_pos _).le | exact le_rfl
  refine budget_fiberwise p hf (fun i s hs => ?_) (h x)
  by_cases hx : x ∈ X i
  · rw [if_pos hx]
    let W := Real.exp (A*coverNumber M (X i))
    calc
      _ ≤ ∑ j∈s, g j * W := sum_le_sum fun j hj => by
        split
        next he' =>
          by_cases hz : g j=0
          · simp only [hz,zero_mul,le_refl]
          have hY := he j hz; rw [hs j hj] at hY
          apply mul_le_mul_of_nonneg_left _ (hg j)
          exact Real.exp_monotone (mul_le_mul_of_nonneg_left
            (by exact_mod_cast Lattice.Corona.cover_mono hY M) ha)
        next he' => exact mul_nonneg (hg _) (Real.exp_pos _).le
      _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (hv _ s hs) (Real.exp_pos _).le
  rw [if_neg hx,Finset.sum_eq_zero];
  intro j hj; split
  next he' =>
    have hz : g j=0 := by
      by_contra h
      have hv := he j h he'; rw [hs j hj] at hv; contradiction
    rw [hz,zero_mul]
  next he' => rfl

/-- Combine whole alphabets even of different types/prices. -/
lemma together (X : ι → Support c) (Y : κ → Support c) (M : ℕ) {w : ι → ℝ} {v : κ → ℝ}
    {A γ ν : ℝ} (h : Ac.Hit X M w A γ) (hh : Ac.Hit Y M v A ν) :
    Ac.Hit (Sum.elim X Y) M (Sum.elim w v) A (γ+ν) := by
  intro x
  let b := unitPrice (Sum.elim X Y) M (Sum.elim w v) A x
  have he j : 0 ≤ b j := by
    rcases j with j|j
    · exact (h x).1 j
    exact (hh x).1 j
  refine budget_of_sum he fun s => ?_
  have eq : s=s.toLeft.disjSum s.toRight := by
    ext j; rcases j with j|j <;> simp
  nth_rewrite 1 [eq]; rw [sum_disjSum]
  exact add_le_add (budget_sum (h x) _) (budget_sum (hh x) _)

section Input
variable {G : Gauge} (p : Ratio c f) (l B : ℕ)

-- Coarsening comparison examples on exactly the existing types.

def regularCore (A : Activities G f) := fun i => (A.reg i).support
def forcedCore (A : Activities G f) := fun i => (A.forced i).support

theorem regular (A : Activities G f) (b : BudgetPoint) {γ : ℝ} (h : A.EBound b γ) :
    ∃ w : ℕ → ℝ, (∀ i, b.supBounds (A.reg i).site (regularCore A i) (A.E i) (w i)) ∧
    Anchored (fun i => (A.reg i).site) w (fun i => coverNumber b.B (regularCore A i)) b.supportExponent γ ∧
    ∀ p : Ratio c f, ∀ l B : ℕ, ∀ C a ε : ℝ, 0 ≤ C → reserve b.supportExponent a (conversion p l) ε →
    0 < B → b.B ≤ 2*B → ∀ (k : ℕ) (g : ℕ → ℝ) (Y : ℕ → Support c),
      (∀ i, Y i ⊆ enlargement p l B (regularCore A i)) → (∀ i,0 ≤ g i) →
      (∀ i, g i ≤ C*w i*(1+(coverNumber b.B (regularCore A i):ℝ))^k) →
      Ac.Hit Y B g a (payment (p.count.val^4) (extentCost l B) k ε C γ a (preCost l)) := by
  obtain ⟨w,hw,hh⟩ := h
  have he : Anchored (fun i => (A.reg i).site) w (fun i => coverNumber b.B (regularCore A i))
      b.supportExponent γ := by
    intro x
    convert hh x using 1
    ext i; simp [BudgetPoint.mass,regularCore,mul_comm]
  refine ⟨w,hw,he,fun p l B C a ε hC hr hB hs k g Y hy hg hG => ?_⟩
  exact coarsen p l B b.B (regularCore A) _ (fun i => (A.reg i).anchor) w
    (fun i => (hw i).1) he Y hy hB hs hC hr k g hg hG

theorem forced (A : Activities G f) (b : BudgetPoint) {γ : ℝ} (h : A.KBound b γ) :
    ∃ w : ℕ → ℝ, (∀ i, 0 ≤ w i ∧ ∀ U, ‖A.K i U‖ ≤ w i) ∧
    Ac.Hit (forcedCore A) b.B w b.supportExponent γ ∧
    ∀ p : Ratio c f, ∀ l B : ℕ, ∀ C a ε : ℝ, 0 ≤ C → reserve b.supportExponent a (conversion p (l+5)) ε →
    0 < B → b.B ≤ 2*B → ∀ (k : ℕ) (g : ℕ → ℝ) (Y : ℕ → Support c),
      (∀ i, Y i ⊆ enlargement p l B (inspected (forcedCore A i))) → (∀ i,0 ≤ g i) →
      (∀ i, g i ≤ C*w i*(1+(coverNumber b.B (forcedCore A i):ℝ))^k) →
      Ac.Hit Y B g a (payment (p.count.val^4) (extentCost (l+5) B) k ε C γ a (preCost (l+5))) := by
  obtain ⟨w,hw,hh⟩ := h
  have h1 i := (hw i).1
  have he : Ac.Hit (forcedCore A) b.B w b.supportExponent γ := by
    intro x; convert hh x using 1
    ext i; simp [BudgetPoint.mass,forcedCore,mul_comm]
  refine ⟨w,hw,he,fun p l B C a ε hC hr hB hs k g Y hy hg hG => ?_⟩
  choose o ho using fun i => (A.forced i).inventory_ne
  have hk i := (A.forced i).inventory_sup (ho i)
  exact coarsen p (l+5) B b.B (forcedCore A) o hk w h1 (anchor_weaker _ _ h1 he o hk) Y
    (fun i => Finset.Subset.trans (hy i) (inspected_price p l B (forcedCore A i) hB)) hB hs hC hr k g hg hG
end Input
end YM.Push.AbsoluteSums.Labels
