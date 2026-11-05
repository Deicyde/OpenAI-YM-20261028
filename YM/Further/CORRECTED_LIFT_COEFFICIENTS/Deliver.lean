import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Basis
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Tape
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Funding

/-!
# Use Reader for all corrected subsets, same portfolio
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Function Lattice Wilson Labels RG Cells Source Filter Extraction RG.Supply
open Push.Corrected Push.CutoffProjectors
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S : Table C.book} {d m k N p : ℕ}

/-- Cutoff choices ONE basis, all letters. `scan` assessed only where
really calibrated. May be padded e.g. by 0 for unused N/k/p.
-/
structure Fleet (X : Columns C S d) where
  B : Series C
  place : Placed X B
  enough : C.ref d ≤ B.depth 0
  scan (k N p : ℕ) : Mat C d

namespace Fleet
variable {X : Columns C S d} (F : Fleet X)





variable (h : C.Makes)
def tape (k N p : ℕ) : Reader C d := Reader.readTape h F.B k N p (F.scan k N p)

def prize (R : Reader C d) : (Cells.standard C).Field d →L[ℂ] C.label d :=
  (R.xi : Mat C d).comp (ladder C d)

lemma prize_real (R : Reader C d) (H) x : star (prize R x)=prize R ((Cells.standard C).conj H d x) := by
  unfold prize; rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,ladder_conj]; exact (R.inter.real _).symm


def tests : Tests X where
  B := F.B
  room := F.place
  tune k N p i := prize (F.tape h k N p) (X.basis i)
  real k N p i := by rw [prize_real _ X.H, X.realBasis]
  unit k N p := by rw [X.initial,prize,ContinuousLinearMap.comp_apply,ladder_unit]; exact Reader.identity_of_unit _










end Fleet
end YM.Further.CorrectedLift
