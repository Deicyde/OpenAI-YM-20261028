import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Lap
import YM.Push.ABSOLUTE_SUMS.Animals

/-!
# Ordered positions in determinant chains

Uniform over colors/arrays/fields in the step; density of
physical addresses includes projection from EVERY fine residue, by a
(permissibly post-L) constant. A zero-cost route need not have these
bounds on its footprint. Uses `Ac.Hit` for further connectivity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Laps
open Win Push.AbsoluteSums Animals RG Lattice Corona Matrix Finset
open scoped BigOperators Classical

variable {Y X n : Type*} [Fintype Y] {u : Side} (d : Y → Site u)

/-- Maximal displacement can include window, orientation or path tests
about the vertex, post-prediction halos etc. Choose before `L` if used
for inherited cover conversion too. -/
def coat (b : ℕ) (i : Y) : Support u := neighbors b (d i)

def sector (b : ℕ) : (k : ℕ) → Y → (Fin k→Y) → Y → Support u
  | 0,i,_,j => coat d b i ∪ coat d b j
  | k+1,i,s,j => coat d b i ∪ sector b k (s 0) (Fin.tail s) j

def straight (b : ℕ) : (k : ℕ) → Y → (Fin k→Y) → Y → Prop
  | 0,i,_,j => separation (d i) (d j) ≤ b
  | k+1,i,s,j => separation (d i) (d (s 0)) ≤ b ∧ straight b k (s 0) (Fin.tail s) j

def Narrow (b : ℕ) (A : Tile Y n) := ∀ i j, sectionOf A i j≠0 → separation (d i) (d j) ≤ b

section
variable [Fintype n]

omit [Fintype Y] in
lemma straight_of_ne {A C : Tile Y n} {b : ℕ} (h : Narrow d b A) (he : Narrow d b C) (k : ℕ)
    (i j : Y) (s : Fin k→Y) (hr : routeF A C k i s j ≠ 0) : straight d b k i s j := by
  induction k generalizing i with
  | zero => exact he i j hr
  | succ k ih =>
    rw [routeF] at hr
    exact ⟨h _ _ (left_ne_zero_of_mul hr), ih (s 0) (Fin.tail s) (right_ne_zero_of_mul hr)⟩
end

section geometry
variable (b k : ℕ) (i j : Y) (s : Fin k→ Y)

omit [Fintype Y] in
lemma contains : d i∈sector d b k i s j ∧ d j∈sector d b k i s j ∧
    ∀ m, d (s m)∈sector d b k i s j := by
  have ht (i : Y) : d i ∈ coat d b i := (neighbors_mem ..).mpr (by simp)
  induction k generalizing i with
  | zero => exact ⟨mem_union_left _ (ht i),mem_union_right _ (ht j),fun m => nomatch m⟩
  | succ k ih =>
    obtain ⟨h1,h2,h3⟩ := ih (s 0) (Fin.tail s)
    exact ⟨mem_union_left _ (ht i),mem_union_right _ h2,fun m => mem_union_right _ (Fin.cases h1 h3 m)⟩

omit [Fintype Y] in
lemma density_cost {B l : ℕ} (hB : 0<B) (he : straight d (l*B) k i s j) :
    coverNumber B (sector d (l*B) k i s j) ≤ (k+2)*ballCost l := by
  have hs i : coverNumber B (coat d (l*B) i) ≤ ballCost l := tile _ _ _ hB
  have hx i : d i∈coat d (l*B) i := (neighbors_mem ..).mpr (by simp)
  induction k generalizing i with
  | zero =>
    have ht : d j∈coat d (l*B) i := (neighbors_mem ..).mpr he
    apply (meets_sum ht (hx j) _).trans; have h1 := hs i; have h2 := hs j; omega
  | succ k ih =>
    change _∧_ at he
    obtain ⟨hb,hv⟩ := he
    have ht : d (s 0) ∈ coat d (l*B) i := (neighbors_mem ..).mpr hb
    apply (meets_sum ht (contains d (l*B) k (s 0) j (Fin.tail s)).1 _).trans
    apply le_trans (Nat.add_le_add (hs i) (ih _ _ hv)); nlinarith

omit [Fintype Y] in
lemma extent_cost (he : straight d b k i s j) {x : Site u} (hx : x∈sector d b k i s j) :
    separation (d i) x ≤ b*(k+2) := by
  induction k generalizing i with
  | zero =>
    rcases mem_union.mp hx with h|h
    · have hi := (neighbors_mem b (d i) x).mp h; omega
    have hi := (neighbors_mem b (d j) x).mp h; apply (separation_triangle (d i) (d j) x).trans
    unfold straight at he; omega
  | succ k ih =>
    rcases mem_union.mp hx with h|h
    · have hi := (neighbors_mem b (d i) x).mp h; nlinarith
    change _ ∧ _ at he; obtain ⟨h1,h2⟩ := he
    have hl := ih _ (Fin.tail s) h2 h; apply (separation_triangle (d i) (d (s 0)) x).trans; nlinarith
end geometry

/-- All orders even at repeated physical positions. -/
abbrev History (Y : Type*) (k : ℕ) := Y × (Fin k→Y) × Y








end YM.AnalyticNext.ConnectedActivity.Laps
