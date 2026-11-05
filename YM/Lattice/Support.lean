import YM.Lattice.Box
import Mathlib.Logic.Relation

/-!
# The native support price

We choose connectedness of unions in the grid graph with
max-distance edges.

Winding paths will remember actual path length elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Lattice

abbrev Support (n : Side) := Finset (Site n)

variable {n : Side}

theorem pdist_step (i : Axis) : pdist (step i : Site n) ≤ 1 := by
  apply Finset.sup_le; intro j _
  simp only [lift, step_apply]; split
  · rw [ZMod.valMinAbs_natAbs_eq_min]
    exact (min_le_left _ _).trans (by rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le ..)
  · simp

theorem walk_conn (x : Site n) (W : Walk) :
    Relation.ReflTransGen (fun a b : Site n => separation a b ≤ 1) x (stop x W) := by
  induction W generalizing x with
  | nil => exact .refl
  | cons d w ih =>
    apply Relation.ReflTransGen.head _ (ih (x + d.vec))
    rw [separation_comm, separation, add_comm, add_sub_cancel_right, Step.vec]
    split
    · rw [pdist_neg]; exact pdist_step _
    exact pdist_step _

theorem wrap_stop_cover (x : Cover) (W : Walk) : wrap n (stop x W) = stop (wrap n x) W := by
  induction W generalizing x with
  | nil => rfl
  | cons d w ih => rw [stop, ih, map_add, wrap_vec, stop]

def halo (M : ℕ) (X : Support n) : Support n := Finset.univ.filter fun y =>
  (X.filter fun x => separation x y ≤ M).Nonempty

theorem halo_spec {M : ℕ} {X : Support n} {y} : y ∈ halo M X ↔ ∃ x ∈ X, separation x y ≤ M := by
  simp [halo, Finset.Nonempty]

theorem halo_subset (M : ℕ) (X : Support n) : X ⊆ halo M X := fun x hx => halo_spec.mpr ⟨x,hx,by simp⟩

/-- Full union of M-balls (not induced subgraph on the centers). -/
def covers (M : ℕ) (X D : Support n) :=
  let A := halo M D
  X ⊆ A ∧ ∀ x ∈ A, ∀ y ∈ A, Relation.ReflTransGen
    (fun u v : Site n => u ∈ A ∧ v ∈ A ∧ separation u v ≤ 1) x y

theorem covers_some (M : ℕ) (X : Support n) : ∃ k : ℕ, ∃ D, covers M X D ∧ D.card = k := by
  refine ⟨_, Finset.univ, ⟨fun x _ => halo_subset M _ (Finset.mem_univ x), fun x _ y _ => ?_⟩, rfl⟩
  let w := route (lift x) (lift y) 1
  have he : stop x w = y := calc
    _ = stop (wrap n (lift x)) w := by rw [wrap_lift]
    _ = wrap n (stop (lift x) w) := (wrap_stop_cover ..).symm
    _ = y := by unfold w; rw [route_end,wrap_lift]
  rw [← he]
  refine Relation.ReflTransGen.mono ?_ x _ (walk_conn x w)
  intro a b h
  exact ⟨halo_subset _ _ (Finset.mem_univ _), halo_subset _ _ (Finset.mem_univ _), h⟩

open scoped Classical in
/-- Minimum number of native `M`-balls with connected union covering X. -/
def coverNumber (M : ℕ) (X : Support n) : ℕ := Nat.find (covers_some M X)

theorem coverNumber_realized (M : ℕ) (X : Support n) :
    ∃ D, covers M X D ∧ D.card = coverNumber M X := by
  classical
  exact Nat.find_spec (covers_some M X)

/-- Strict anchored chart on the torus in native sites (about the tag, not
post hoc recentering). Within this box use `lift (x-o)`. -/
def Nonwrapping (X : Support n) (o : Site n) := ∀ x ∈ X, 10 * separation x o < n.val

/-- Endpoints need both vertices. -/
theorem agrees_mono {M N : Set (Site n)} {K : Type*} {U V : Links (Per n) K}
    (h : Agrees M U V) (he : N ⊆ M) : Agrees N U V := fun e a b => h e (he a) (he b)
end YM.Lattice
