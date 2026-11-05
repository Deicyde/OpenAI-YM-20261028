import Mathlib.Analysis.Complex.Schwarz
import YM.Push.LOOP_COEFFICIENT.Pullback

/-!
# Based paths for scalar two-curvature rows, normalization and cap

Precision row as input, hence action atoms use half its value. Change only
the `loop` field of the supplied output PathData. Not a proof of classical
matching for the supplied rows.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Set Matrix Lattice Laurent Bloch RG Exterior Wilson
open scoped Topology InnerProductSpace BigOperators ContDiff

abbrev Label := (Fin 2 → PlaqAxes) × Cover

def labels : ℕ ≃ Label := by
  haveI : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩
  letI := Classical.choice (nonempty_denumerable Label)
  exact (Denumerable.eqv Label).symm



variable {G : Gauge} (R : Row (TypeFace 2) (TypeFace 2)) (u : Label)
def payment := R (plaquette (u.1 0)) (plaquette (u.1 1)) u.2 / 2

def ticket (G : Gauge) : Atom G 2 := { leg := ![⟨[], u.1 0⟩, ⟨route 0 u.2 1,u.1 1⟩], coeff x := if x 0 = x 1 then payment R u else 0 }







def renew (T : PathData G) : PathData G := { T with loop i := ticket R (labels i) G }






variable {R} {η C : ℝ}




variable {T : PathData G}







end YM.Push.Loops
