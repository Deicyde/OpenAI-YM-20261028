import YM.Ac.Tree
import YM.SectorNext.RECONNECTED_LOCALITY.Parts

set_option warningAsError false

/-!
# Passing the pins up through trees (packet gain not necessarily at the root)

Absolute support-exponential budgets on the actual cover.
Including the *per occurrence* cover sum version of these estimates (needed still before
summing derivatives). Assumes actual hit costs at input, doesn't assert that they hold for
dictionaries of step formulas. Distinct-address connected subset part here. Need first to
group whenever trying to use a *shared physical event's gain just once*; don't give each
component an independent factor or charge output flags that don't occur in its inventory.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
namespace Ledger

open Lattice RG Filter Function Words
open scoped Classical

variable {ι ν : Type*} {c : Side} {X : ι → Support c} {B : ℕ} {w f : ι → ℝ} {a b γ δ : ℝ}

lemma pinsFromFinite (h : ∀ i,0 ≤ f i) (he : ∀ s : Finset ι,∑ i∈s,f i ≤ γ) : SumBudget f γ := by
  have hs := summable_of_sum_le h he
  exact ⟨h,hs,hs.tsum_le_of_sum_le he⟩

lemma reduce (h : ∀ i,0 ≤ f i) (hm : ∀ i,f i ≤ w i) (he : SumBudget w γ) (hv : γ ≤ δ) : SumBudget f δ := by
  have hs:=he.2.1.of_nonneg_of_le h hm
  exact ⟨h,hs,(hs.tsum_le_tsum hm he.2.1).trans (he.2.2.trans hv)⟩

lemma scalar (ha : 0 ≤ a) (h : SumBudget f γ) : SumBudget (fun i => a*f i) (a*γ) :=
  ⟨fun i => mul_nonneg ha (h.1 i),h.2.1.mul_left a,
   by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 ha⟩

lemma debit (h : SumBudget f a) (hw : SumBudget w b) : SumBudget (fun i => f i + w i) (a+b) := by
  refine ⟨fun i => add_nonneg (h.1 i) (hw.1 i),h.2.1.add hw.2.1,?_⟩
  rw [h.2.1.tsum_add hw.2.1]; exact add_le_add h.2.2 hw.2.2

/-- Reindex a subbudget (no identification of duplicate costs by value or support). -/
lemma renamed {g : ν → ℝ} (f : ι → ν) (hf : Injective f) (h : SumBudget g γ) : SumBudget (g ∘ f) γ := by
  have hs := h.2.1.comp_injective hf
  refine ⟨fun i => h.1 (f i),hs,?_⟩
  exact (Summable.tsum_le_tsum_of_inj f hf (fun i _ => h.1 i) (fun i => le_rfl) hs h.2.1).trans h.2.2







/-- Some entries may have empty footprints only if *known weight zero*, not by convention
of taking a hit sup and then claiming absolute sum. -/
lemma volume_price (hn : ∀ i,0 ≤ f i) (h : Ac.Hit X B f a γ) (hE : ∀ i,f i ≠ 0 → (X i).Nonempty) :
    SumBudget (fun i => f i * Real.exp (a*coverNumber B (X i))) (Fintype.card (Site c)*γ) := by
  refine pinsFromFinite (fun i => mul_nonneg (hn i) (Real.exp_nonneg _)) fun s => ?_
  let F (x : Site c) i := if x∈X i then f i * Real.exp (a*coverNumber B (X i)) else 0
  calc
    _ ≤ ∑ i∈s,∑ x : Site c,F x i := by
      apply Finset.sum_le_sum; intro i _
      by_cases he : f i=0
      · simp only [he,zero_mul]; exact Finset.sum_nonneg fun x _ => (h x).1 i
      obtain ⟨x,hx⟩:=hE i he
      calc
        _ = F x i := (if_pos hx).symm
        _ ≤ _ := Finset.single_le_sum (fun x _ => (h x).1 i) (Finset.mem_univ x)
    _ ≤ _ := by
      rw [Finset.sum_comm]
      apply le_trans (Finset.sum_le_sum (fun x _ => ((h x).2.1.sum_le_tsum s (fun i _ => (h x).1 i)).trans (h x).2.2))
      simp

lemma volume (ha : 0 ≤ a) (hn : ∀ i,0 ≤ f i) (h : Ac.Hit X B f a γ) (hE : ∀ i,f i ≠ 0 → (X i).Nonempty) :
    SumBudget f (Fintype.card (Site c)*γ) :=
  reduce hn (fun i => le_mul_of_one_le_right (hn i) (Real.one_le_exp (mul_nonneg ha (by positivity))))
    (volume_price hn h hE) le_rfl

lemma cover_pos {P : Support c} (h : P.Nonempty) : 0 < coverNumber B P := Nat.pos_of_ne_zero (fun he => by
  have H := Corona.pays P B
  rw [he, Nat.zero_mul] at H
  exact (not_le.mpr (Finset.card_pos.mpr h)) H)

/-- True volume factor used, no real-power ambiguity. -/
def size (B : ℕ) : ℕ := (B+B+1)^4

lemma rel_size (B : ℕ) (P : Support c) : P.card ≤ coverNumber B P * size B := Corona.pays ..

/-- The common tree *test*. Lean fields are exposed (real powers not rpow, actual torus,
true per-placement sums at reserved exponent etc). -/
structure Takes (X : ι → Support c) (B : ℕ) (f : ι → ℝ) (a γ : ℝ) : Prop where
  expN : 0 ≤ a
  pn : 0 ≤ γ
  pos : ∀ i,0 ≤ f i
  backing : Ac.Hit X B f (a+1) γ
  small : (B+B+1:ℕ)^4*(γ:ℝ) ≤ 1

/-- Connected-component weights may carry decisions or be zero. Mere structural
lemma, real `cutEntry`/marginals have to prove this estimate with ALL the masks and tags.
Allows a scale cost on the whole and extracting a factor e.g. eta for ALL forced components. -/
theorem letters (h : Takes X B f a γ) (u : Finset ι → ℝ) (hu : ∀ i,0 ≤ u i)
    (he : ∀ i,u i ≠ 0 → Ac.Spark X i) (b : ℝ) (hb : 0 ≤ b)
    (hp : ∀ s,Ac.Spark X s → u s ≤ b*∏ i∈s,f i) :
    Ac.Hit (region X) B u a (b*(Real.exp γ-1)) := by
  intro x
  refine reduce ?_ ?_ (scalar hb (Ac.forest X B h.expN h.pos h.backing h.small h.pn x)) le_rfl
  · intro i; split
    · exact mul_nonneg (hu _) (Real.exp_nonneg _)
    exact le_rfl
  intro s
  simp only [Ac.roots]
  split_ifs with hx hj
  · calc
      _ ≤ (b*∏ i∈s,f i)*Real.exp (a*coverNumber B (region X s)) :=
        mul_le_mul_of_nonneg_right (hp s hj.1) (Real.exp_nonneg _)
      _ = _ := by ring
  · rw [show u s=0 from not_not.mp (fun hv => hj ⟨he s hv,hx⟩)]; simp
  · exact mul_nonneg hb (mul_nonneg (Real.exp_nonneg _) (Finset.prod_nonneg fun i _ => h.pos i))
  simp

/-- The *sum* of cover numbers of occurrences (well-defined even if paths wrap or are longer
than these prices). -/
def occurred (X : ι → Support c) (B : ℕ) (s : Finset ι) := ∑ i∈s,coverNumber B (X i)

/-- Stronger version with occurrences charged separately incl on repeated spatial positions
(distinct address labels in s), not claiming the cardinality covers path multiplicity. -/
theorem letters_each (h : Takes X B f a γ) (u : Finset ι → ℝ) (hu : ∀ i,0 ≤ u i)
    (he : ∀ i,u i ≠ 0 → Ac.Spark X i) (b : ℝ) (hb : 0 ≤ b)
    (hp : ∀ s,Ac.Spark X s → u s ≤ b*∏ i∈s,f i) (x : Site c) :
    SumBudget (fun s => if x∈region X s then u s * Real.exp (a * occurred X B s) else 0) (b*(Real.exp γ-1)) := by
  let v i := f i * Real.exp (a*coverNumber B (X i))
  let U s := u s * Real.exp (a*occurred X B s)
  have hV : Takes X B v 0 γ := {
    expN:=le_rfl
    pn:=h.pn
    pos:=fun i => mul_nonneg (h.pos i) (Real.exp_nonneg _)
    small:=h.small
    backing:=by
      intro x
      convert! h.backing x using 1
      ext i; split
      · simp only [v,mul_assoc,← Real.exp_add, add_mul]; ring_nf
      rfl }
  have hp' (s : Finset ι) (H : Ac.Spark X s) : U s ≤ b*∏ i∈s,v i := by
    unfold U occurred v
    simp only [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
    push_cast
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hp s H) (Real.exp_nonneg _)
  simpa only [Ac.Hit, zero_mul,Real.exp_zero,mul_one,U] using
    (letters hV U (fun s => mul_nonneg (hu s) (Real.exp_nonneg _)) (fun s H => he s (left_ne_zero_of_mul H)) b hb hp' x)



lemma pays_enlargement {u : Finset ι → ℝ} {Y : Finset ι → Support c}
    (hX : ∀ s,Y s ⊆ region X s)
    (h : Takes X B f (a+b) γ) (ha : 0 ≤ a) (_hb : 0 ≤ b) (hu : ∀ s,0 ≤ u s)
    (he : ∀ s,u s ≠ 0 → Ac.Spark X s) (d : ℝ) (hd : 0 ≤ d)
    (hp : ∀ s,Ac.Spark X s → u s ≤ d * Real.exp (b*occurred X B s) * ∏ i∈s,f i) :
    Ac.Hit Y B u a (d*(Real.exp γ-1)) := by
  let t (s : Finset ι) := if Ac.Spark X s then ∏ i∈s,f i else 0
  have ht : ∀ s,0 ≤ t s := by intro s; unfold t; split; exact Finset.prod_nonneg fun i _ => h.pos i; exact le_rfl
  intro x
  have hs := scalar hd (letters_each h t ht (fun s hv => of_not_not (fun hn => hv (if_neg hn))) 1 zero_le_one (by
    intro s hx; simp [t,hx]) x)
  simp only [one_mul] at hs
  refine reduce (fun s => ?_) (fun s => ?_) hs le_rfl
  · split
    · exact mul_nonneg (hu s) (Real.exp_nonneg _)
    exact le_rfl
  split
  · rename_i hx
    rw [if_pos (hX s hx)]
    by_cases hw : u s=0
    · rw [hw,zero_mul]
      exact mul_nonneg hd (mul_nonneg (ht _) (Real.exp_nonneg _))
    have hl:=he s hw
    unfold t; rw [if_pos hl,add_mul,Real.exp_add]
    have hy : coverNumber B (Y s) ≤ occurred X B s := (Corona.cover_mono (hX s) B).trans (Ac.cover X B hl)
    refine (mul_le_mul (hp s hl) (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hy) ha)) (Real.exp_nonneg _)
      ((hu s).trans (hp s hl))).trans (le_of_eq ?_)
    ring
  split
  · exact mul_nonneg hd (mul_nonneg (ht _) (Real.exp_nonneg _))
  simp





end Ledger
end YM.SectorNext.Reconnect
