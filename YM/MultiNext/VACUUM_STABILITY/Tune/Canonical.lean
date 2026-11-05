import YM.MultiNext.VACUUM_STABILITY.Tune.Local
import YM.Next.FOUNDATIONS.JetReads

set_option warningAsError false

/-! Local checkout at the actual canonical germ. Reuse FOUNDATIONS and pricing at
C (pre-purchases needed). In particular, the uniform tickets for the mask move are available;
no bound assumed on the selected section/projected remainder away from masks. No contraction of
the remainder here; only absolute transfer as needed at `Tenders`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Tune
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Hits Next.Foundations Labels Source
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V : Type} {n : Side} {G : Gauge} {F : SmoothLetter V G n}
namespace Exchange

/-- Stamped, threshold-scaled coordinates. -/
structure Identified (D : Exchange F) {d : ℕ} (A : Labels.Frame G d) (P : BudgetPoint) (H : Hol G)
    (S : SectionData A) (v : A.Coeff) : Prop where
  basis : D.ringSites = S.footprint D.placement
  fiat : D.fiat = v 0
  projection : Reads H D.placement F.zone (A.coords.symm (A.scaled P.threshold⁻¹ v)) F.stamp.ink
  placed : D.portrait=S.places (A.scaled P.threshold⁻¹ v) D.placement
  core : D.right.stamp.ink=S.places (A.scaled P.threshold⁻¹ (A.core v)) D.placement
  lower : D.left.stamp.ink 1=0
  invisible : Nonwrapping D.left.zone D.placement → H.PiVanish d D.placement D.left.stamp.ink







-- Returns a *choice* with true calibrated null/remainder conventions and receipt
-- uniform over value budgets and torus periods.

end Exchange
end YM.Multi.Vacuum.Tune
