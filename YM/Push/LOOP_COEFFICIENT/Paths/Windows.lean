import YM.Push.LOOP_COEFFICIENT.Paths.Reader
import YM.Work.F02.Path

/-!
# Windows for analytic-local angular-coordinate path tests
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Matrix Function Set Filter Metric Lattice Laurent RG Bloch
open scoped Topology ContDiff BigOperators
variable {a b : Type} {r : ℕ}

def Window (r : ℕ) := {x : Cover | size x ≤ r}
lemma window_finite (r) : (Window r).Finite := by
  apply (Set.finite_Icc (fun _ : Axis => -(r:ℤ)) (fun _ : Axis => (r:ℤ))).subset
  have he {x : Cover} (hx : x∈Window r) (j : Axis) : |x j| ≤ r := (Int.natCast_natAbs _ ▸ Int.ofNat_le.mpr ((Finset.single_le_sum (fun i (_:i∈Finset.univ) => Nat.zero_le (x i).natAbs) (Finset.mem_univ j)).trans hx))
  intro x hx; exact ⟨fun i => (abs_le.mp (he hx i)).1,fun i => (abs_le.mp (he hx i)).2⟩
instance (r) : Fintype (Window r) := (window_finite r).fintype
instance (r) : DecidablePred (· ∈ Window r) := inferInstanceAs (DecidablePred (fun x : Cover => size x ≤ r))

abbrev Shifts (a : Type) := Cover → CSpace a

def pad (v : CSpace (Window r × a)) : Shifts a := fun x i => if h : x∈Window r then v (⟨x,h⟩,i) else 0
lemma pad_contDiff [Fintype a] (x : Cover) (i : a) : ContDiff ℂ ω (fun v : CSpace (Window r × a) => pad v x i) := by unfold pad; split <;> first | apply contDiff_apply | apply contDiff_const
lemma pad_norm [Fintype a] (v : CSpace (Window r × a)) (x) : ‖pad v x‖ ≤ ‖v‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => by
  unfold pad; split
  · apply norm_le_pi_norm
  · simp

structure Film (a : Type) where
  radius : ℕ
  value : Shifts a → ℂ
  inside {x y} : (∀ i∈Window radius,x i = y i) → value x = value y
namespace Film
def reader [Fintype a] (f : Film a) : Reader a where
  shape := Window f.radius × a
  range := inferInstance
  leaf := Prod.snd
  offset i := i.1.val
  sizeBound := f.radius
  near i := i.1.property
  value := f.value ∘ pad
lemma wrapped [Fintype a] [Fintype b] (f : Film a) {n : Side} (A : Grid n b a) (x : Site n) (z : CSpace b) :
    f.reader.value (f.reader.gather A x z) = f.value (fun y j => z (A.symm (wrap n y + x,j))) := by
  refine f.inside fun y hy => ?_; funext j; rw [pad,dif_pos hy]; exact congr_arg z (congr_arg A.symm (Prod.ext (add_comm ..) rfl))
end Film
end YM.Push.Loops.Paths
