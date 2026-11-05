import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.Dues
import YM.Next.UV_STRESS.Birth
import YM.Next.UV_STRESS.Foundation
import YM.Push.BETA_TRANSPORT.Gibbs
import YM.Push.COMMON_WITNESSES.Fields
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.PRICE_COMPILER.Suppression

/-!
# At the Hosted seam -- keep the actual UV witnesses

Never assume Grill from arbitrary Covers, nor hit a Furnace on a different
(say, pre-calibration) trajectory simply to apply UVStress.foundation.
Re-use the *joint approximation* already bought on the Hosted side. Nothing
here asserts that Rank/Grill bills for Hosted, or weak and stress bills for
the normalized hierarchy, can physically be paid.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Grade
open Set Function Filter Extraction Table Ward Climb Org Spec
  Next.Extract Next.UVStress Push.Common Snap
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f g : Extraction.Order} {S : Table C.book}
variable {w : Snap C} {u : Upper w} {b : Presentation C} {Q : Guests u.T} {W : MaxwellData C} {I : IR (C:=C) u.T}

/-- Give Common its exact Grades and expose the same (centered, nonzero) J &
Scaling, at THIS W normalization. -/
theorem pricing (H : Hosted u b Q f) (W : MaxwellData C) (hF : FreeDiv W.T W.hT W.lit.hers)
    (hu : Stations C f W.hT.spin)
    (hb : ∀ J : KernelSpace H.seed.kernel.spin, J.val ≠ 0 → Conserved u.V H.seed.kernel.spin J.val → Probed f J.val) :
    ∃ (I : IR (C:=C) u.T) (X : Scaling u.T), I.J ≠ 0 ∧ I.J ∈ KernelSpace H.seed.kernel.spin ∧ Probed f I.J ∧
      Approaches (path X) (isoPanel X) ∧ Stable H.seed.kernel.spin W.hT.spin u.V W.T.W X ∧
        X.meter I.J W.T.J ∧ Grades H.atBase W I := by
  have e := H.seed
  obtain ⟨-,I,X,hI,hJ,hP,hX,hY,hM,h₁,h₂⟩ := current_ready e.cutoff e.ordered e.generic e.kernel e.copies
    H.atBase.base.clean.ready H.atBase.base.clean.tilt (cap_given e.corrected)
    W.T W.hT W.lit.edges W.lit.pales W.lit.hers hF hu hb
  exact ⟨I,X,hI,hJ,hP,hX,hY,hM,h₁,h₂⟩

/-- Link same-field receipts, with no requirement on the boundary witnesses,
K lift, nor any sector-ring theorem outside this H. Calibration is for this C
(shared from the cutoff/band hypotheses). Z.sector.energy here may *differ*
from I.J (unnormalized one); keep Z whole, including Tab & its retuned
energy value. `Playing.delivers` is exactly `Spec.Final` on this order. -/
structure Encore (u : Upper w) (b : Presentation C) (Q : Guests u.T) (W : MaxwellData C)
    (I : IR (C:=C) u.T) (Z : Cast u W I) (f : Extraction.Order) (X : Scaling u.T) : Prop where
  stage : Playing u b Q W I Z f
  frequency : Stations C f W.hT.spin
  current : I.J≠0 ∧ I.J∈KernelSpace stage.estimates.seed.kernel.spin
  path_ : Approaches (path X) (isoPanel X)
  coherence : Stable stage.estimates.seed.kernel.spin W.hT.spin u.V W.T.W X
  calibration : X.meter I.J W.T.J








end YM.UVNext.Grade
