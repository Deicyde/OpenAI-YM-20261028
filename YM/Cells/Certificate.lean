import YM.Slice.Reflection
import YM.Cells.Chess

/-!
#  cell RP base, established
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells
open Function Set Filter MeasureTheory
open Lattice Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable (G : Gauge) (n : Side) (β : ℝ)
structure Seam : Prop where
  positive : ∀ C : Cut n, Positive G β C
  inequality (T : Tiling n) (F : T.Cell → Config G n → ℂ) (h : ∀ i, Interior (T.chamber 0) (F i)) :
    ‖moment β (fun x => ∏ i, T.copy i (F i) x)‖ ≤ ∏ i, T.rootTest β (F i)
  semi (T : Tiling n) (F F' : Config G n → ℂ) (H : Interior (T.chamber 0) F) (h : Interior (T.chamber 0) F') :
    T.rootTest β (F+F') ≤ T.rootTest β F + T.rootTest β F'

theorem laws (h : 0 ≤ β) : Seam G n β where
  positive _ := Slice.reflected_positive _ β h
  inequality T F hf := T.tiles β (fun _ _ => Slice.reflected_positive _ β h) F hf
  semi T F P hf hp := T.adds β (fun _ _ => Slice.reflected_positive _ β h) F P hf hp
end YM.Cells
