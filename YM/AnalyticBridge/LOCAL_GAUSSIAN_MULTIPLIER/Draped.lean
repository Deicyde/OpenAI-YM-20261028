import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Hard

/-!
# Commission some genuine held-U atoms from the inherited RG purchase

Includes fine profile, predictor likelihood, K, q and masked E (for
holding *all* its possibly hard arguments). Thus can buy them for
this joint test if they retain the required chart support, etc.; do not
transfer to a singleton E-jet gain/contraction after expansion. Also
don't charge a sited cap once per Z coordinate. No pre-L regularity
or oscillation claim on the input ligand constants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube
  ProjectorNext.Equivariance Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
  YM.Push.SectorMeasure YM.Next.Foundations Precision MeasureTheory Metric Curtain
open Spot Viewport Notice
open scoped Topology BigOperators Matrix.Norms.Frobenius YM.Push.SectorMeasure ContDiff Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {u : Spot d}
    {H R K : Type} {X : Support c} {l : Viewport u X H R K}
    [Fintype H] [Fintype R]
    {O r : ℝ} {k : ℕ} {p : Reel G H R K} {U : Config G c}

namespace Notice
variable (a : Notice l)





























lemma knows_connector (u : Spot d) (j : Bond c) (h : S.patch.Branches S.kernel G) : LocalOn (predictorUses S j) (u.connectorBit j) := by
  intro V W he; have hx := YM.Push.GridApprox.connector_dep S h j u.k.1 u.k.1 rfl rfl
    (fun e hi hh => he e (Or.inl hi) (Or.inl hh)) (fun e hi hh => he e (Or.inr hi) (Or.inr hh))
  unfold Spot.connectorBit; rw [hx]


end Notice
end YM.AnalyticBridge.LocalGaussian
