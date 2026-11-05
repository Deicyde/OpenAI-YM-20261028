import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Embrace
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Statue


/-!
# Compile contacts at the physical t radius from inputs on C

Getting R_0 coupons: polynomial powers of M, late discounts in E(kpc),
requires actual calendar payments on columns (don't substitute logScale
for monitor!), plus free covariance estimates. Does not claim station etc
from those. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.Dollars
open Filter Function Set Lattice Wilson Labels RG Cells Source Source.Drops Extraction
open Work Push.Corrected Push.CutoffProjectors Collapse PathCost Building Growth Fund Next.Foundations
open Stone Statue 
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {m d k N p l t : ℕ} {C : Family G}

abbrev M (C : Family G) (m : ℕ) := C.path.levels.clock.coverSize m
def construct (M : ℕ) := M*(4*M+2)+2*M








variable {W : ℕ}

def paradigm (h : distant (C.side m p) (construct (M C m))) (l : ℕ) (Q : Copper G (C.side m p)) := Compass.adjunct
    (C:=C) (p:=p) (m:=m) (see G l h (C.path.levels.budget m)) (slides G h _ l) Q





-- One native dimension bound, independent of calendar. Absorb max card,
-- leg costs (incl extra turn steps), and wall^2 for derivative rate.







end YM.Further.CorrectedLift.Dollars
