import YM.Next.EXTRACTION.Raw
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Hybrid

set_option warningAsError false

/-!
# From the mixed and singleton budgets to Radial in the same history

Do not pay a global count for the number of labels when combining the two
budgets. Only the per-i prices at the actual rooted sizes delivered at
output. Here c,b given to the invoice, additionally impose a single room bill
for the singleton dictionary. Quantitative reading uses only true `p`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror.Marketing
open Set Filter Function MeasureTheory RG Wilson Lattice Cells Marker Overlay Tower Net Masked Stop
open Labels Source
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

section Charge
variable {S Y : Type*}







end Charge
section Receipts
variable {G : Gauge} {C : Family G} {p m l N d : ℕ}

/-- Pays the extra canonical part of a singleton entry at the actual
mask section, including the `p` mass exponent. Fixed multiplier can be
large depending on stage. -/
def priceOne (C : Family G) (d l : ℕ) :=
    let c := (C.path.levels.params l).columns
    1 + c * Real.exp ((C.path.levels.budget l).supportExponent * (Masked.size C d+Masked.size C d+1:ℝ)^4)


def shrink (C : Family G) (l : ℕ) := Real.sqrt (C.path.levels.clock.forcedAllowance l)


/-- A single-voice receipt specifies a budget a measured BEFORE multiplying
by current marker radius. h.prices can pay even the actual, but masked,
canonical coefficients. Meas includes K/E gauges from Sound/Format.
-/
structure Counters (X : Mixed C N p m l) (Q : Singles C p m l d) (a : ℝ) : Prop where
  appoint (i) : ∃ v, (Q i).Format (X.origins i) C.params (C.path.rep N p l) ∧
    (Q i).remBound (X.origins i) (C.path.rep N p l) (shrink C l) v ∧ v+(Masked.R C d).coeffSize (Q i).x ≤ a



section Reserve
variable (X : Mixed C N p m l)


end Reserve
end Receipts
end YM.ProjectorNext.RMirror.Marketing
