import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.PhysicalNext.ORDERED_AFFINE_2B.Support

/-!
# Direction reads for the same streams on ALL coordinates.

Keep every answer to every query in these sets (initial sites with ALL
endpoint allowances). Do not need to suppose remote hard configurations
realizable to prove these dependence properties. Use later only with
Standing/matched etc for prices! `Follow` gives a congruence method for
**the same** signed list of direction calls, tested only through the
numeric radius of a row. Full frame-factor effects on overlapping slots
then need no more reads than advertised. Not an exponential gain for
summing/integrating Z, or permission to use just entry-anchors instead
of the full B-dependent footprints in incidence tests. Foreground radius
`allN`, seed+partner-query radius `signalH`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Footprint
open Function Filter Set Lattice Wilson RG Pressure Precision Exterior Tree
open AnalyticBridge AnalyticBridge.Covariance AnalyticBridge.Covariance.Terrain
open Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps
open Push.SectorMeasure Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ}
    {V V' : Config G c} {A A' : Stores S} {F F' : Forest S.ratio} {k k' : S.Choices} {T : Tube G S}
    {q : Chi} {d : ℝ} {o : Site c} {n r : ℕ}
    {Y : LinkArray G (Frozen A x F)} {Y' : LinkArray G (Frozen A' x F')}

/-- Outer + endpoint/flag read support. Among the answers retained are
also the values of V on every edge of every plaquette which could touch
a queried flag site; do not charge the flag-read exception in this proof.
`n` in uses is numerical radius, `r` the decision radius. At a fuller
packet symmetrize over all requests, not just a nonzero realized stencil.
-/
structure Archive (S : StepData c f) {F F' : Forest S.ratio} {A A' : Stores S} {x : ℝ}
    (o : Site c) (n r : ℕ) (k k' : S.Choices) (V V' : Config G c) (Y : LinkArray G (Frozen A x F)) (Y' : LinkArray G (Frozen A' x F')) : Prop where
  numerical : Shared S o n r k k' V V' Y Y'
  queryV : AgreeNear id o (r+10) V V'
  -- keep even this (numbers never used here), on full records
  heights : ∀ i, separation o (S.ratio.parent i) ≤ r → F.height i=F'.height i






namespace Padded
variable (q : Chi) (d g : ℝ)




end Padded
end YM.PhysicalNext.OrderedAffine2B.Footprint
