import YM.Lattice.Faces
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Pi.Interval

/-! Ordinary patch operations on the lattice cover. -/

set_option autoImplicit false
namespace YM.Lattice
open Finset

def box (r : ℕ) : Finset Cover := Icc (fun _ => -(r : ℤ)) (fun _ => (r : ℤ))

@[simp] theorem box_test {r : ℕ} {x : Cover} : x ∈ box r ↔
    (∀ i, - (r : ℤ) ≤ x i) ∧ (∀ i, x i ≤ (r : ℤ)) := mem_Icc

@[simp] theorem center_box (r : ℕ) : 0 ∈ box r := by simp

theorem box_covariant (r : ℕ) (s : Signed) : (box r).image s.act = box r := by
  have he (h : Signed) (x : Cover) (ha : x ∈ box r) : h.act x ∈ box r := by
    simp only [box_test, Signed.act] at *; constructor
    all_goals intro i; split
    · exact neg_le_neg (ha.2 _)
    · exact ha.1 _
    · simpa only [neg_neg] using neg_le_neg (ha.1 (h.perm.symm i))
    · exact ha.2 _
  ext x; rw [mem_image]
  constructor
  · rintro ⟨y,hy,rfl⟩; exact he s y hy
  intro hx; exact ⟨_, he s⁻¹ x hx, s.act_inv x⟩

/-- Leg with integer signed length in axis `a`. -/
def straight (a : Axis) (d : ℤ) : Walk := List.replicate d.natAbs ⟨a,decide (d<0)⟩

def axisRoute (x y : Cover) (l : List Axis) : Walk :=
  l.flatMap fun a => straight a (y a - x a)

abbrev Order := Equiv.Perm Axis

def allAxes (l : Order) := (List.finRange 4).map l


def route (x y : Cover) (l : Order) : Walk := axisRoute x y (allAxes l)

theorem straight_stop (x : Cover) (a : Axis) (d : ℤ) : stop x (straight a d) = x + d • step a := by
  have h (x : Cover) (n : ℕ) (s : Step) : stop x (List.replicate n s) = x + n • s.vec := by
    induction n generalizing x with
    | zero => simp [stop]
    | succ n ih => rw [List.replicate_succ, stop, ih, succ_nsmul]; abel
  rw [straight, h]; congr 1
  by_cases hl : d < 0
  · simp only [hl, decide_true]
    rw [show (Step.vec ⟨a,true⟩ : Cover) = - step a from rfl]
    have hd : (d.natAbs : ℤ) = -d := by omega
    rw [smul_neg, ← Nat.cast_smul_eq_nsmul ℤ _ _]
    rw [hd, neg_smul, neg_neg]
  · simp only [hl, decide_false]
    rw [show (Step.vec ⟨a,false⟩ : Cover) = step a from rfl]
    have hd : (d.natAbs : ℤ) = d := by omega
    rw [← Nat.cast_smul_eq_nsmul ℤ _ _, hd]

theorem axisRoute_end (x y z : Cover) (l : List Axis) (h : l.Nodup) :
    stop z (axisRoute x y l) = fun i => z i + if i ∈ l then y i - x i else 0 := by
  induction l generalizing z with
  | nil => simp [stop, axisRoute]
  | cons a l ih =>
    funext i
    have e := List.nodup_cons.mp h
    rw [show axisRoute x y (a::l) = straight a (y a-x a) ++ axisRoute x y l from rfl,
      stop_append, straight_stop, ih _ e.2]
    rcases eq_or_ne i a with H|H <;> simp [*, Pi.smul_apply]

theorem route_end (x y : Cover) (l : Order) : stop x (route x y l) = y := by
  unfold route
  rw [axisRoute_end]
  · funext i
    have e : i ∈ allAxes l := List.mem_map.mpr ⟨l.symm i, by simp, by simp⟩
    simp [e]
  exact (List.nodup_finRange _).map l.injective

@[simp] theorem route_same (x : Cover) (l : Order) : route x x l = [] := by simp [route, axisRoute, straight]
end YM.Lattice
