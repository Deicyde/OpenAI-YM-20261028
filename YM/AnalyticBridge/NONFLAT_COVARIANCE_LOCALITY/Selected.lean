import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Epoch
import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Gap
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen


/-!
# Selected kernel

D is the actual V-dependent formula (predictor with authentic inputs and shared
tags, not assumed constant in V). Calibration here uses post-L constants and
the `temp x` output-flag threshold. The preceding estimates require nonempty coordinates nowhere.
Read the Epoch type (matrix conclusions in common occurrence-line currency)
before using for local ratios. All decay and gap constants are fixed-L after
the displayed choices and prior to waiting. Nothing here estimates a kernel
on a sector with incompatible flags using its own V evaluation. Only a fixed
mask extension may reach such parameters near a valid center.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Matrix Function Filter Lattice RG Wilson Pressure Tree
open Next.SectorChange Next.SectorChange.Schur Next.SectorChange.Wisps
open FreeResolvent Mark TestD
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- SC's *specific* window-choice `fog` on its V extension. -/
def sector (x : ℝ) (A : Stores S) (F : Forest S.ratio) (V : Config G c)
    (k : S.Choices) (T : Tube G S) (z : Coord G c) :=
  fog A F T x (coarse V z) k


/-- Earned at a true step. Geometry fixed throughout each Epoch.
Reachable heights don't follow from Epochs alone; this is a purchase
BEFORE Bar/Wait. -/
structure Accepted (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) (r t η γ C x : ℝ) : Prop where
  geometry : 120 ≤ radiusB x
  epoch : ∀ {c f : Side} (S : StepData c f), S.patch=P → 100*(1+radiusB x) ≤ c.val →
      ∀ (T : Tube G S), Pt.Funds S T →
        ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c), A.flags=RG.flags (temp x) V →
          ∀ (k : S.Choices) (z : Coord G c), ‖z‖ ≤ r →
          Epoch (front A F) (panels A F) x (precision x A F V k T) (sector x A F V k T)
            z n t η γ C



end YM.AnalyticBridge.NonflatCovarianceLocality
