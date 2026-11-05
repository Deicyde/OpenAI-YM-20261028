import YM.Extra.FREE_DETECTOR_ALGEBRA.Forest

set_option warningAsError false

/-!
# Bringing the detecting fields together, off the target insertion

Equality of factor counts rules out self-contractions in the coalescing
bunch. This file uses that condition for an actual limit (no OPE
assumptions at coincident sites).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {G : Gauge} {n : ℕ}

def shorten (v : Fin n→ WickPol G) (i : Fin n) (a : Slot G) := update v i (pderiv a (v i))









section pull
variable {p q : E4}








end pull

variable {x y : E4}


end YM.Extra.FD
