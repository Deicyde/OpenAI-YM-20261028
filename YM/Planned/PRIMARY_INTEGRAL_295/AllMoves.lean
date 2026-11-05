import YM.Extra.SOURCE_HISTORIES.Motion
import YM.Push.LOCAL_SPLITTING.Transport


/-! # Transporting a projection and its density on every Signed / Bool orbit

Always through the REAL, SAME cube, threshold, tag choices,
prepayment B Actual vacuum. Apply to caller `P` only. Does not assume
unitary or isometry estimates in label l1 currency; charge orbitCost for
that. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.AllMoves
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Next.Foundations Extra.Histories
open Push.Local
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {n : Side} {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {o : Site n} {R : Rep G n} {A : Hol G}
variable {P : Coefficient F n}

def refill (P : Coefficient F n) : Coefficient F n where
  x := star P.x
  support := P.support
  regular i := star (P.regular i)
  forced i := star (P.forced i)









-- Applies any actual Moves proof; preserves addresses literally through it.
def pose (P : Coefficient F n) (y : Motion) (o : Site n) (M : R.activities.Moves y.1 o) :=
    if y.2 then refill (reorient M P) else reorient M P






end YM.Planned.PrimaryIntegral295.AllMoves
