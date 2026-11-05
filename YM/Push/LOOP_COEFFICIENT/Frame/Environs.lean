import YM.Push.LOOP_COEFFICIENT.Block.Duplicate

/-!
# Shift recipes for patch fields in their centered coordinates
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Set Filter Matrix Lattice Laurent Bloch RG Wilson Precision Exterior Complex Block Portal
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {P : Patch} {c f L : Side}

abbrev spanJ (P : Patch) := P.J+6
abbrev Zone (P : Patch) := ↥(box (spanJ P))
abbrev Interior (P : Patch) (G : Gauge) := Zone P × VectorBlock G P.L
abbrev Satellite := Option Axis
def location : Satellite → Cover := Option.elim' 0 step
abbrev Outlook (P : Patch) (G : Gauge) := Interior P G ⊕ Axes G
abbrev LocalField (P : Patch) (G : Gauge) := Interior P G ⊕ (Satellite × G.ColorIndex)




def region (L : Side) (x : Cover) : Cover := (cover_of_eq (lift (wrap L x)) x (wrap_lift _)).choose



abbrev Fits (P : Patch) (x : Cover) := region P.L x ∈ box (spanJ P)






variable {a R : Type}
def locate [Zero R] (P : Patch) (v : Zone P × Co P.L a → R) (x : Cover) (i : a) : R := if h : Fits P x then v (⟨_,h⟩,wrap P.L x,i) else 0


variable {g : Ratio c f} {T : Cross P.L (TypeFace 1) (TypeFace 1)}







end YM.Push.Loops.Frames
