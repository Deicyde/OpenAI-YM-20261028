import YM.Next.ROTATIONS.Response
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Shift


/-!
# The two common-coordinate laws (helpers for the weighted comparison)

Counting `Gaussian.Vec` with the *literal* `SectorChange.Gaussian.cloud`.
Compare in normalized coordinates: restore `b + g • y` from **both**. For
nonflat local mean `a` this means the law of y on covariance marginal C is
that of `δ+Z`, where `δ = g⁻¹ • (a-b)` and `Z ~ cloud C`. For free mean b
the law is just `cloud B` of its covariance marginal B. Projection is on
the covariance and any repeated/color powers later are tests on that same
joint law (not new cloud calls).

`replace C B (-δ) y`: target *shifted C* vs reference *centered B*, y the
common normalized read. Thus its *argument shift parameter* is `-δ`; the Z
of C is at `y-δ`, not `y+δ`. We also give the exact identities for actual
raw reads from the two full-register measures, including change-of-density
(which then assesses that ratio at `g⁻¹ • (x-b)`). Need g nonzero to use
these conversions. See Workshop file for the actual slots and means.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C
open Function Filter Set Matrix MeasureTheory
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian
 
open SectorTools
open SectorTools.PhysicalGaussianSwitch (shift)
open scoped Topology BigOperators ENNReal

section likelihood

variable {I : Type} [Fintype I] [DecidableEq I] (C B : Gaussian.Table I) (δ : Vec I)





variable {C B}





variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]



end likelihood

section raw

variable {I J : Type}

def restoreRead (b : Vec I) (g : ℝ) (z : Vec I) : Vec I := b + g • z

def normalizeRead (b : Vec I) (g : ℝ) (x : Vec I) : Vec I := g⁻¹ • (x-b)

/-- Canonical shift of target normalized by the common center b. -/
def changeMean (a b : Vec I) (g : ℝ) : Vec I := g⁻¹ • (a-b)

/-- Raw physical read from the WHOLE cloud. -/
def physicalRead (a : Vec I) (g : ℝ) (e : J ↪ I) (z : Vec I) : Vec J := (a + g • z) ∘ e












variable [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J]
variable {Q : Gaussian.Table I}









end raw
end YM.PhysicalNext.WeightedGaussianMarginal45C
