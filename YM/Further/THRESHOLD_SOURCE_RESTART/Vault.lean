import YM.Next.BOUNDARY.Alias
import YM.Next.EXTRACTION.Relay
import YM.Next.FOUNDATIONS.SU2
import YM.Push.CORRECTED_COLUMNS.Pieces
import YM.Work.B17
/-!
# Include vacuum price and bound every decorated entry

A K lease on an actual hard `Original`, earned from its *complete* listings
(per decoration, attached occurrences and vacuum). `Escrow` is a per-site
budget with exponential cover cost, never per site for each marker-mode
independently. Even passing from a root bill on the marks to this vault
costs a cover exponent and an occupancy factor below. The forced divisor
reserves should be chosen accordingly. In particular these are inputs in
addition to any bare unmarked lawfulness requirement. No lower bounds on
individual vacuum K values, no ratio of marker coefficients to them.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart
open Function Filter MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected  Width 
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V : Type*} [DecidableEq V] {R : Census V}
variable {P : Rep G n} {o : V → Site n} {w : V → ℝ}

/-- Also used in the uncorrected and corrected session income. -/
abbrev KSite (P : Rep G n) (i : ℕ × ℕ) := oldSites P i.1
structure VacuumReserve (P : Rep G n) (M : ℕ) (a b : ℝ) : Prop where
  funds : ∃ g : ℕ → ℝ, (∀ i,0 ≤ g i ∧ ∀ U, ‖P.activities.K i U‖ ≤ g i) ∧
    Ac.Hit (oldSites P) M g a b



/-- Value entry accounting on one hard polynomial. Produce stamp and keep
locality even for blank occurrences (pin test as in `Value` for nonzero entries). `Vault` gives
stamp and K evaluation; does not assume summability in the identity.
-/
structure Vault (P : Rep G n) (o : V → Site n) (R : Census V) where
  hard : Original P o R
  mark : ℕ × ℕ → R.Mode
  key (q) : (mark q).val.Nonempty
  entry : ℕ × ℕ → Config G n → ℂ
  localK (q) : Width.LocalCharge P.p o (KSite P q) (fun U => Poly.send (mark q) (entry q U))
  admitted (q U) : entry q U ≠ 0 → permits P q.1 U
  full i U : hard.value i U= Poly.send R.quiet (P.activities.K i U:ℂ) +
      ∑' j, Poly.send (mark (i,j)) (entry (i,j) U)

namespace Vault
variable (F : Vault P o R)



variable {M : ℕ} {a b c : ℝ}










end Vault
end YM.Further.ThresholdSourceRestart
