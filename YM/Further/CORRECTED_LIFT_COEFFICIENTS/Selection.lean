import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Deliver
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Symbol
/-!
# Give the actual scan, not a bound-only hypothesis

Choose with data where promised, even if the conditions hold only in ordered
late sense; total on unspecified cutoffs by explicitly marked padding.
This uses the same covariance and board choices (not asserting they are
available). Later inputs on Offer (e.g. Crew, and actual trajectory
transport at the smaller threshold), if using this construction, must use these same Y's, costs and Wick
symbols. We don't assert any success of those estimates under arbitrary choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Filter Function Lattice Wilson RG Source Source.Drops Labels Next.Extract Extraction Cells
open Push.Corrected Push.Corrected.Issue Push.CutoffProjectors Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {C : Family G} {S : Table C.book} {d m k N p t : ℕ}

/-- Symbols only where testing. Fits requested Taylor degree t. -/
structure Won (C : Family G) (d m N p t : ℕ) where
  A : Portfolio C m p t
  face : A.Faith d N
  cert : A.tight d (1/2)

-- `Fuel` interacts with the later supplier: no uniqueness asserted of
-- the optics. Can match prechosen path conventions at this interface.
abbrev Scouting (B : Series C) (d t : ℕ) := ∀ k N p : ℕ, Option (Won C d (B.depth k) N p t)

namespace Scouting
variable {X : Columns C S d} {B : Series C} {f g : Extraction.Order}
variable (gifts : Scouting B d t)









variable (h : C.Makes) (hP : Placed X B) (hr : C.ref d ≤ B.depth 0)

def fleet : Fleet X where
  B := B
  place := hP
  enough := hr
  scan k N p := match gifts k N p with
    | some H => H.A.readout H.face h
    | none => 0








end Scouting
end YM.Further.CorrectedLift
