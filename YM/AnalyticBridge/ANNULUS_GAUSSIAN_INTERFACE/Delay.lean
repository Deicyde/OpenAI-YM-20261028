import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Payment
import YM.Next.ROTATIONS.Tunnel
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Handoff

set_option warningAsError false

/-!
# Epmult even with same price gates (RScene, before realizing Directed)

One example of a joint bill of the ring already transmitting, Gaussian
windows in `SectorChange` and annulus charge. Boost BEFORE Wait. Absence
of red consumers in this proof important; only claim obtained level
usable as in `Step` if later actually purchased. H an *extra* reserved
budget e.g. for controlling ancillary factors per analytic heading. Not
claiming all those costs are compatible.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus.Delay
open Function Filter Set Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Input RG.Supply RG.Shoot Next.Scheduling Pressure.Testing Next.SectorChange
open YM.SectorNext.Remainder.Scales
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} (Z : ChartRatio G) (K : MapPrices) {B : Sheet G} (D : Rolls B)
    {T : Protection D}



/-- The associated energy κ is determined (some receipt) before
βEntry, not that of an even later existential call to Ringing. -/
structure Buffer (j i : ℕ) (low w a E H κ : ℝ) (n m : ℕ) : Prop where
  pos : 0<κ ∧ 0<w
  cosmos : Starcash Z K D low j i w a E
  transmits : ∀ x ≥ low, ∀ (c f : Side) (S : StepData c f), S.patch.J=j → S.patch.L=D.L j →
    Payment S.patch (query B K j i) Z w κ H n m a x ∧
    (100*(1+radiusB x)≤c.val → ∀ U : Tube G S, (query B K j i).Funds S U → PointCharge U x w κ)



variable {D}
structure Buys (W : Delays T) (g a E H κ : ℕ → ℕ → ℝ) (n m : ℕ → ℕ → ℕ) : Prop where
  adjacent j i : Adj j i → B.first ≤ i → Buffer Z K D j i (W.betaEntry j) (g j i) (a j i) (E j i) (H j i)
    (κ j i) (n j i) (m j i)



end YM.AnalyticBridge.Annulus.Delay
