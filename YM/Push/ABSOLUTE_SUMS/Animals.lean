import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.LinearAlgebra.Trace
import YM.Corona.Fill
import YM.Gauge.MatrixGroup

/-!
# Counting connected finite supports by walks

Used, in particular, for the mandatory defect alphabet (cf. fcpct/). Doesn't require injectivity of any geometric placement built
from coordinates/offsets. Use the *actual typed vertices* and an upper
bound on their (also typed) neighbors. Degree zero, stuttering etc OK.

Also a crude native bound for ANY supports counted by `coverNumber`,
even if the support itself is not connected. Note the entropy constant's
dependence on the radius; in particular we aren't proposing counting
arbitrary subsets of halos against FIXED small support exponents!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Animals
open YM.Lattice YM.Lattice.Corona Relation Finset
open scoped Topology BigOperators

section Walks
variable {α : Type*} [DecidableEq α] (N : α → Finset α)

def trails (x : α) : ℕ → Finset (List α)
  | 0 => {[x]}
  | m+1 => (N x).biUnion (fun y => (trails y m).image (List.cons x))

lemma trails_card {D : ℕ} (hn : ∀ x, (N x).card ≤ D) (m : ℕ) (x : α) :
    (trails N x m).card ≤ D^m := by
  induction m generalizing x with
  | zero => simp [trails]
  | succ m IH =>
    rw [trails, pow_succ']
    apply Finset.card_biUnion_le.trans
    apply (sum_le_sum (f:=fun y => ((trails N y m).image (List.cons x)).card)
      (fun y _ => Finset.card_image_le.trans (IH y))).trans
    simpa using Nat.mul_le_mul_right (D^m) (hn x)

lemma prepend (x y : α) (h : y ∈ N x) (m : ℕ) {w : List α} (hw : w∈trails N y m) :
    x :: w ∈ trails N x (m+1) := by
  rw [trails]
  exact mem_biUnion.mpr ⟨y,h,mem_image_of_mem (List.cons x) hw⟩

private lemma splice (a b : α) (hb : b∈N a) (ha : a∈N b) (m : ℕ)
    (x : α) (w : List α) (hw : w ∈ trails N x m) (hh : a∈w) :
    ∃ v ∈ trails N x (m+2), v.toFinset = insert b w.toFinset := by
  have he {m x w} (hw : w∈trails N x m) (hr : x=a) (hh : a∈(w : List α).toFinset) :
      a :: b :: w ∈ trails N x (m+2) ∧
      (a :: b :: w).toFinset = insert b w.toFinset := by
    subst x
    refine ⟨prepend N a b hb (m+1) (prepend N b a ha m hw), ?_⟩
    simp only [List.toFinset_cons]; exact Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hh)
  induction m generalizing x w with
  | zero =>
    obtain rfl : w=[x] := by simpa only [trails, mem_singleton] using hw
    obtain ⟨hz,hz'⟩ := he hw (by simpa [eq_comm] using hh) (List.mem_toFinset.mpr hh)
    exact ⟨_,hz,hz'⟩
  | succ m IH =>
    rw [trails] at hw
    obtain ⟨y,hy,h⟩ := mem_biUnion.mp hw
    obtain ⟨w,hw2,rfl⟩ := mem_image.mp h
    by_cases hn : x=a
    · obtain ⟨hz,hz'⟩ := he (prepend N x y hy m hw2) hn (List.mem_toFinset.mpr hh)
      exact ⟨_,hz,hz'⟩
    obtain ⟨v,hv,he⟩ := IH y w hw2 (by simpa [Ne.symm hn] using hh)
    refine ⟨x :: v, prepend N x y hy (m+2) hv, ?_⟩
    simp only [List.toFinset_cons, he]; rw [Finset.insert_comm]

def Linked (s : Finset α) : Prop := ∀ i∈s, ∀ j∈s, ReflTransGen
  (fun a b => a ∈ s ∧ b ∈ s ∧ b ∈ N a) i j

lemma list_animals (hn : ∀ {x y : α}, x∈ N y → y∈N x) (s : Finset α)
    (hs : Linked N s) (x : α) (hx : x∈s) (m : ℕ) (hm : s.card=m+1) :
    ∃ w ∈ trails N x (2*m), w.toFinset=s := by
  have H (k : ℕ) (hk : k+1≤ s.card) : ∃ w ∈ trails N x (2*k),
      x ∈ w.toFinset ∧ w.toFinset ⊆ s ∧ w.toFinset.card=k+1 := by
    induction k with
    | zero => exact ⟨[x],by simp [trails],by simp,by simp [hx]⟩
    | succ k IH =>
      obtain ⟨w,hw,hx',hh,hK⟩ := IH (by omega)
      let U := w.toFinset
      obtain ⟨b,hb,hB⟩ := Finset.exists_mem_notMem_of_card_lt_card (show U.card<s.card by
        change w.toFinset.card<s.card; omega)
      have he : ∀ j, ReflTransGen (fun a b => a∈s ∧ b∈s ∧ b∈N a) x j → j∉U →
          ∃ l∈U,∃ y∈s,y∉U ∧ y∈N l := by
        intro j hj; induction hj with
        | refl => exact fun H => absurd hx' H
        | @tail a b _ h IH =>
          intro hb; by_cases ha : a∈U
          · exact ⟨a,ha,b,h.2.1,hb,h.2.2⟩
          exact IH ha
      obtain ⟨a,ha,y,hy,hY,hn'⟩ := he b (hs x hx b hb) hB
      obtain ⟨v,hv,H'⟩ := splice N a y hn' (hn hn') _ _ _ hw (List.mem_toFinset.mp ha)
      have eq : 2*(k+1)=2*k+2 := by ring
      refine ⟨v,eq ▸ hv, ?_⟩
      rw [H',card_insert_of_notMem hY,hK]
      exact ⟨mem_insert_of_mem hx',insert_subset hy hh, rfl⟩
  obtain ⟨w,h1,h2,h3,h4⟩ := H m hm.ge
  exact ⟨w,h1, eq_of_subset_of_card_le h3 (by omega)⟩

/-- Each set counted once, no matter how many spanning walks. -/
lemma animals_succ (hn : ∀ {x y : α}, x∈N y → y∈N x) {D : ℕ}
    (he : ∀ x, (N x).card ≤ D) (u : Finset (Finset α)) (s : Finset α) (k : ℕ)
    (hu : ∀ a∈u, a.card=k+1 ∧ Linked N a ∧ ∃ x∈a, x∈s) :
    u.card ≤ s.card * D^(2*k) := by
  let t (x : α) := (trails N x (2*k)).image List.toFinset
  have h : u ⊆ s.biUnion t := by
    intro a ha; obtain ⟨hh,hl,x,hx,hz⟩ := hu a ha
    obtain ⟨w,hw,H⟩ := list_animals N hn a hl x hx k hh
    exact mem_biUnion.mpr ⟨x,hz,mem_image.mpr ⟨w,hw,H⟩⟩
  calc
    _ ≤ ∑ x ∈ s, (t x).card := (Finset.card_le_card h).trans (Finset.card_biUnion_le)
    _ ≤ ∑ _x ∈ s, D^(2*k) := sum_le_sum fun x _ => Finset.card_image_le.trans (trails_card N he _ _)
    _ = _ := by simp



lemma animals (hn : ∀ {x y : α}, x∈N y → y∈N x) {D : ℕ} (hD : 1 ≤ D)
    (he : ∀ x, (N x).card ≤ D) (u : Finset (Finset α)) (s : Finset α) (k : ℕ)
    (hu : ∀ a∈u, a.card=k ∧ Linked N a ∧ ∃ x∈a, x∈s) :
    u.card ≤ s.card * (D^2)^k := by
  cases k with
  | zero =>
    have h : u=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun a ha => by
      obtain ⟨h1,h2,x,hx,-⟩ := hu a ha
      have he := card_pos.mpr (show a.Nonempty from ⟨x,hx⟩)
      omega)
    simp [h]
  | succ k =>
    rw [← pow_mul]
    apply (animals_succ N hn he u s k hu).trans
    gcongr
    omega
end Walks

section Lattice

open scoped Classical

variable {n : Side}

def neighbors (b : ℕ) (x : Site n) := halo b {x}
/-- Keep this four-dimensional ball-volume polynomial explicit. -/
def ballCost (b : ℕ) : ℕ := (b+b+1)^4

lemma neighbors_mem (b : ℕ) (x y : Site n) : y ∈ neighbors b x ↔ separation x y ≤ b := by
  simp only [neighbors, halo_spec, Finset.mem_singleton]; simp

-- NOTE: Site n already has a DecidableEq, we make no classical instance changes.
lemma neighbors_back (b : ℕ) {x y : Site n} : y ∈ neighbors b x → x ∈ neighbors b y := by
  rw [neighbors_mem, neighbors_mem, separation_comm x y]; exact id

lemma neighbors_card (b : ℕ) (x : Site n) : (neighbors b x).card ≤ ballCost b := by
  simpa only [neighbors,ballCost,card_singleton,one_mul] using halo_size ({x} : Support n) b

lemma neighbors_ge (b : ℕ) : 1 ≤ ballCost b := by
  have h : 0 < ballCost b := by unfold ballCost; positivity
  exact h

lemma price_zero (M : ℕ) : coverNumber M (∅ : Support n) = 0 :=
  Nat.eq_zero_of_le_zero (by
    apply le_trans (Corona.list_cost (D:=∅) _ ?_) (by simp)
    have h : halo M (∅ : Support n) = ∅ := by ext; simp [halo_spec]
    simp [covers,h])

lemma price_pos (M : ℕ) (X : Support n) : 0 < coverNumber M X ↔ X.Nonempty := by
  constructor
  · intro h; by_contra he
    rw [not_nonempty_iff_eq_empty.mp he, price_zero] at h
    omega
  intro h; have he := Corona.pays X M
  contrapose! he
  have hy := card_pos.mpr h
  rw [Nat.eq_zero_of_le_zero he]; simpa

















end Lattice

end YM.Push.AbsoluteSums.Animals
