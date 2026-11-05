import YM.MergeProof.West.Horns
import YM.TraceExtension.Prom.Front.West.Expose
import YM.TraceExtension.Prom.Front.West.Mural
import YM.TraceExtension.Prom.Front.West.Throne
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Port.Soft.Spear
/-!
  Variant of YM.MergeProof.West.Horns for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open YM.Next.Rank.Tapes.West
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    AnalyticBridge.GaussianFieldAlignment.Locations SectorNext.Vacuum
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps Display Display.Docking
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {N i p k : ℕ}
local notation "St" => C.path.levels.clock.op i p
local notation "D" => C.path.levels
local notation "x" => C.path.levels.clock.hatBeta i
local notation "y" => C.path.levels.clock.hatBeta (i+1)
def SpearSky.a_pprove {B : Binding C} {g : Course C N p k} {l : Purse} {n U z}
    {P Q H} (p' : SpearSky B g l (i:=i) H U z P Q) (m : C.Makes)
    (X : Points n) (Y : Lantern G St) : IgnFtSky (short B N p) l.band X g H p'.duty l.era.coast.Q l.horizon
      P.p Q.p (l.sends (Atlas.clim D k)) := by
  refine ⟨fun i' V hV => ?_⟩
  let b:= Fintype.card (Streak Y.park); let A:= Fintype.equivFin (Streak Y.park)
  refine ⟨b,fun j => e_xposeSky B m H g l.era.coast.Q n X p'.duty p'.canvas i' V rfl rfl p'.price
       ?_ p'.warmth Y.χ Y.heat Y.bright (A.symm j).wood (A.symm j).tag, fun j=>(A.symm j).share,fun j => Streak.share_nn _,?_⟩
  · rw [p'.sparks,p'.budget] at hV; exact hV
  exact (Equiv.sum_comp A.symm Streak.share).trans (Streak.full (C.path.levels.blocks i p).branches)
end YM.PhysicalNext.InteractingRank.Soft
