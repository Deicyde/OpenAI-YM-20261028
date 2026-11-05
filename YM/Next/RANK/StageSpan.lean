import YM.Next.RANK.Reward
import YM.Work.I01


/-!
# Restoration at the middle of the A comparison

Actual position of marker ancestor required inside each H or K. Cubes Q_i possibly
cover large areas of torus, but measured in cover radius have small costs.
L separation counted on the actual cyclic torus, including seam copies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Camp
open Lattice Wilson RG Marker Glyph EntryWord Value Finset
open scoped Topology BigOperators Classical

variable {n : Side} {A : Type} [DecidableEq A] [Fintype A] {V : Type} [DecidableEq V] [Fintype V]

-- nonempty subsets of all local markers have possible W entries
abbrev flame (V : Type) [Fintype V] [DecidableEq V] := {i : modes V // i.val.Nonempty}

-- careful instances ordering
lemma fire_size : Fintype.card (flame V) ≤ 2^(Fintype.card V) := by
  apply (Fintype.card_subtype_le _).trans; refine le_of_eq ?_
  have he : modes V ≃ Finset V := ⟨Subtype.val,scene,fun _ => rfl,fun _ => rfl⟩
  rw [Fintype.card_congr he]; simp

-- Order of args implicit; choose Fintype so univ is well-formed even when no labels.

def sectionAt (i : A × flame V) : modes (A × V) := push i.1 i.2.val

def touchedBy (Q : A → Support n) (P : Support n) := univ.filter fun i => ¬ Disjoint (Q i) P

def audience (T : modes (A × V)) : Finset A := T.val.image Prod.fst

def singled (T : modes (A × V)) := (audience T).card ≤ 1

lemma counted (T : modes (A × V)) : T.val.card ≤ (audience T).card*Fintype.card V := by
  have hx : T.val ⊆ audience T ×ˢ univ := fun i hi => mem_product.mpr ⟨mem_image_of_mem _ hi, mem_univ _⟩
  exact (card_le_card hx).trans_eq (card_product ..)

variable (Q : A → Support n) (ζ : A × V → Site n)

lemma included (hu : ∀ i,ζ i∈Q i.1) (P : Support n) (x : modes (A × V))
    (he : ∀ i, i∈x.val → ζ i∈P) : audience x ⊆ touchedBy Q P := by
  intro i hi; obtain ⟨j,hj,rfl⟩ := mem_image.mp hi; apply mem_filter.mpr
  exact ⟨mem_univ _,fun h => disjoint_left.mp h (hu j) (he j hj)⟩

def rearranged (ζ : A × V → Site n) (Q : A → Support n) (B : ℕ) :=
  (∀ i,ζ i ∈ Q i.1) ∧ 8≤B ∧ ∀ j i, i≠j → ∀ x ∈ Q j, ∀ y ∈Q i, B^2 ≤ separation x y

variable {Q ζ}

omit [DecidableEq A] [Fintype A] [DecidableEq V] [Fintype V] in
lemma pairwise {B : ℕ} (hh : rearranged ζ Q B) (x : Site n) (i j : A) (hi : x∈Q i) (hj : x∈Q j) : i=j := by
  apply Classical.byContradiction; intro he
  have hp := hh.2.2 j i he x hj x hi
  have hz := hh.2.1; have ht : 0<B^2 := pow_pos (by omega) _; simp at hp; omega

omit [DecidableEq V] [Fintype V] in
lemma dispersal {B : ℕ} (hh : rearranged ζ Q B) (P : Support n) (hp : 2 ≤ (touchedBy Q P).card) :
    B*(touchedBy Q P).card ≤ 64*coverNumber B P := by
  have hv : ∀ i∈touchedBy Q P, ∃ x∈Q i,x∈P := fun i hi => not_disjoint_iff.mp (mem_filter.mp hi).2
  choose! y hy hz using hv
  apply YM.Work.I01.answer _ A y B hh.2.1 (touchedBy Q P) (fun i hi j hj he => hh.2.2 i j (Ne.symm he) _ (hy i hi) _ (hy j hj)) hp P
  rintro x hx; obtain ⟨i,hi,rfl⟩ := mem_image.mp hx; exact hz i hi

omit [DecidableEq V] [Fintype V] in
lemma dispersal_cost {B : ℕ} (hh : rearranged ζ Q B) (P : Support n) {a u : ℝ} (ha : 0 ≤ a) (hc : 64*u ≤ a*B)
    (hp : 2 ≤ (touchedBy Q P).card) : u*(touchedBy Q P).card ≤ a*coverNumber B P := by
  have he : (B:ℝ) * (touchedBy Q P).card ≤ 64*coverNumber B P := by exact_mod_cast dispersal hh P hp
  linarith only [mul_le_mul_of_nonneg_left he ha,mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (touchedBy Q P).card : 0 ≤ ((touchedBy Q P).card:ℝ))]

-- Cost converted from at v. If K multi-position paid with only upfront few marks,
-- a Refusal on the bad mask can be handed a debit in addition.

variable {G : Gauge}
variable {p : BudgetPoint} {W : A × flame V → Refusal G ζ p.threshold} (hh : ∀ i,(W i).extent=Q i.1)
include hh in
lemma sworn (P : Support n) : (promises W P).card = (touchedBy Q P).card * Fintype.card (flame V) := by
  have hx : promises W P = touchedBy Q P ×ˢ univ := by ext ⟨i,j⟩; simp [promises,touchedBy,hh,disjoint_comm]
  rw [hx,card_product]; rfl

end YM.Next.Rank.Camp
