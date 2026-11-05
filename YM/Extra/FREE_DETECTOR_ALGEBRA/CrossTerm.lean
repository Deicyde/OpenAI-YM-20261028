import YM.Extra.FREE_DETECTOR_ALGEBRA.Fuse
import YM.Extra.FREE_DETECTOR_ALGEBRA.Laurent
import YM.Extra.FREE_DETECTOR_ALGEBRA.Undo

set_option warningAsError false

/-! Extract two-leg nearby insertions entirely at separated configurations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD.OPE
open Function Filter Set Tensor Analysis Maxwell Wick Pair Residue SphereTest
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {G : Gauge} {j k n m : ℕ}





def stageTwo (x : Points n) (W : Fin n → WickPol G) (i : Fin n) (a : Slot G) (q : Fin n) (b : Slot G) : ℂ :=
    moment G x (shorten (shorten W i a) q b)









/-- Magnitudes of negative powers in this test. -/
def rung (j : ℕ) (i : Slot G) : ℕ := j+i.1+4

def residueSingle (P : Sol G.Color j) (Q : Sol G.Color k) (v : E4) (h : ℕ) (x y : E4) (i b : Slot G) :=
    if h≤rung j i then ether P i v * Residue.grade (fun t : ℝ => ether Q b (x+t • v-y)) (rung j i - h) else 0
















end YM.Extra.FD.OPE
