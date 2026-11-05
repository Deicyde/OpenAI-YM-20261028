import Mathlib
import YM.Next.FREE_KERNELS.Signal
import YM.Next.SCHEDULE.Dues
import YM.Next.UV_STRESS.Across
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.PRICE_COMPILER.Authors


set_option warningAsError false

/-!
# Price on a natural concrete currency for dial-independent vacuum reset templates:

No input asserting that the output E, or even the pre-reset bulk R, are constructible.
Test the UNMASKED log jet germs read via actual ordered increments. Need P.supBounds plus
smoothness at flat, charge curvature directions in the same units as that estimate, no
automatic license for a larger probe. Use no read of a Hessian on a winding edge path for
which the test isn't called for.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.BranchTuning.AffinePay
open Lattice Wilson RG Shoot Function Filter  Next.Foundations 
open scoped Matrix.Norms.Frobenius BigOperators Topology ContDiff Classical
variable {G : Gauge} {n : Side} {P : BudgetPoint} {ι : Type*}

structure Lens (P : BudgetPoint) (G : Gauge) (n : Side) (ι : Type*) where
  source : ℕ → RegularAddress n
  /-- unscaled test (scaled by threshold when charging) -/
  test : ι → Site n → Directions G n
  fits (j : ι) (o : Site n) : P.dirBound o (P.threshold • test j o)
  affine (j : ι) (o : Site n) : IsAffineDirection o (test j o)

variable (L : Lens P G n ι) (S : Activities G n)









variable {S}




/-! parameter variation estimates unnormalized -/

variable {r : ℕ}



end YM.AnalyticBridge.BranchTuning.AffinePay
