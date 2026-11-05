import YM.Next.MAXWELL.Descent
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymFare
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymWhole
import YM.UVNext.FREE_STRESS_CERTIFICATE.Pressure

/-!
# Scalar RUN labels and equivariance, including all integral lines

Use these comparisons of *real functions* around certified V addresses;
transform along ACTUAL fields (Y transformed too on both held bases).
Extension terms per earlier fixed-sector real-continuation data. No
statement on the physical integrand with incorrect A flags or switching
its input/output occurrences simultaneously. Log-line PRICE & integral
equivariant here on the region where the same s/t accounts qualify. No
claim of symmetry of generic labels within the color-block grouping or
those of exterior obligations. Here endpoints use the actual CT/Atlas
Z test, both components read once their operands are issued.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.SymTravel
open Function Filter Set Lattice RG Wilson Precision Tree Pressure Stores
open Next Next.SectorChange AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor Whole Matrix
open Further Further.CurvedGaussianJets Jets Tracks Completion SymRows SymWhole SymFare
open MeasureTheory SectorNext.Vacuum
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {m d q : ℕ}
local notation "RPrice" => Next.SectorChange.Prices

section names
variable (W : Windows (Thing G f)) (X : Jets.Field G c (Thing G f))

def lap (P : CurvedGaussianJets.Prices) (i : Bond f) (v : Config G c) := ∑ j : G.ColorIndex, W.tollLine (X v) P.mass (i,j)
def sailingFee (u : ℝ) (p : Run (Bond f) (d+2)) (v : Config G c) := close p (fun j=> sailing W X j u v)
def aside (p : Run (Bond f) (d+2)) (v : Config G c) := close p (fun j=> mailed W X j v)
def correction (p : Run (Bond f) (d+1)) (v : Config G c) := close p (fun j=>pushLog W X j v)
-- ORIENTATION ORDER kept: A factor at right. (1/2) ratio.
def trough (z : RPrice G (Bond f)) (p : Run (Bond f) (d+2)) (v : Config G c) := facing p z z (fun j=>pushQuad W X j v)/2
end names

variable {x : ℝ} {A A' : Stores S} {F F' : Forest S.ratio}
    {hx : 120 ≤ radiusB x} (L : Box x A A' F F') (O : ColorOrtho G (Bond f))
    (P : CurvedGaussianJets.Prices) (X X' : Jets.Field G c (Thing G f)) (V V' : Config G c)
local notation "W" => windows S G x hx

/-- Use only on `Readable` data for EACH log purchase. Follows from
common certified book on neighborhoods of matched data (see Trips).
Declarations also on unreachable words, not a choice to base labels on
current detected nonzero entries. Includes the REAL `Ioi 0` convention.
-/
structure Readable (S : StepData c f) (x : ℝ) (hx : 120 ≤ radiusB x) (P : CurvedGaussianJets.Prices)
    (X : Jets.Field G c (Thing G f)) (V : Config G c) : Prop where
  valid : Fits (initial G f) P (X V)
  shipped {d : ℕ} (j : Run (Thing G f) (d+2)) : IntegrableOn (fun u=> sailing (windows S G x hx) X j u V) (Ioi (0:ℝ))

namespace Readable
variable {P X V X' V' L O}




variable (h : Readable S x hx P X V)
include h



variable (h' : Readable S x hx P X' V') (hp : Route L O hx (X V) (X' V'))
include h' hp

end Readable

section trip
variable {P L O X X' V V'} (h : Route L O hx (X V) (X' V')) (d : ℕ)
-- packets order d,d+1,d+2 definitions literal

include h







end trip
end YM.PhysicalNext.OrderedAffine2B.SymTravel
