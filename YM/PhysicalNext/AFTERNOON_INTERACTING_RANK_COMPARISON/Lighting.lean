import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Emulation
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Orchards

/-!
# Buying Ignition for actual smaller calls along Rank

Pose from all indicated tagRef/forest draws. On the *fixed* Course,
W unspecified at all marks. Keep ordering across other Choir obligations.
`Pole.approve` BEFORE W compilation/log. Doesn't assert that this family
and Course was constructible, nor does Ignition itself require or procure
any density estimates. See downstream Festival and Opacity/Musters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    AnalyticBridge.GaussianFieldAlignment.Locations SectorNext.Vacuum
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
variable {C : Family G} {N i p k : ℕ}
local notation "St" => C.path.levels.clock.op i p
local notation "D" => C.path.levels
local notation "x" => C.path.levels.clock.hatBeta i
local notation "y" => C.path.levels.clock.hatBeta (i+1)

/-- Pole is a call already on a Course, before any marker refinement.
Scope counts still fixed. -/
structure Pole (B : Binding C) (g : Course C N p k) (purse : Purse)
    (H : i<k) (U z : ℝ) (P : Rep G (C.side (i+1) p)) (Q : Rep G (C.side i p)) : Prop where
  duty : Station.middle D purse.band k ≤ i
  hired : C.path.levels.clock.J (i+1)=C.path.levels.clock.J i
  canvas : roomTest D purse.band k p purse.horizon purse.era.coast.Q
  price : Dawn (C.path.levels.clock.op i p).patch (tell B i) (B.prices.α (C.path.levels.clock.J i)) (B.prices.η (C.path.levels.clock.J i)) (B.prices.Ω (C.path.levels.clock.J i))
      purse.era.coast.Q U z (purse.sends (Atlas.clim D k)) x (g.changeβ (i+1)) (g.changeβ i)
  warming : Perch.Candle g (i+1) P (show i+1 ≤ N from Nat.le_trans H g.allow)
  spark : Perch.Candle g i Q (Nat.le_trans H.le g.allow)



structure Lantern {c f : Side} (G : Gauge) (S : StepData c f) where
  χ : Chi
  hood : ℝ
  heat : 0 < hood
  bright : 2*hood < firstRadius G
  park : Orchard S
instance {c f : Side} (G : Gauge) (S : StepData c f) : Nonempty (Lantern G S) := by
  obtain ⟨L⟩:= Tree.select S.ratio S.patch.odd_side
  have he := first_pos G
  exact ⟨⟨Chi.canonical,firstRadius G/3,by positivity,by linarith,Orchard.alone S L⟩⟩

/-- Use purchases on the actual Pole. Emulator variables and gauges
literally from these preparations, even for Frame/Lantern choices with
which no rewrite has yet been matched. -/
def Pole.approve {B : Binding C} {g : Course C N p k} {l : Purse} {n U z}
    {P Q H} (p' : Pole B g l (i:=i) H U z P Q) (m : C.Makes)
    (X : Points n) (Y : Lantern G St) : Ignition (short B N p) l.band X g H p'.duty l.era.coast.Q l.horizon
      P.p Q.p (l.sends (Atlas.clim D k)) := by
  refine ⟨fun i' V hV => ?_⟩
  let b:= Fintype.card (Streak Y.park); let A:= Fintype.equivFin (Streak Y.park)
  refine ⟨b,fun j => expose B m H g l.era.coast.Q n X p'.duty p'.canvas i' V rfl rfl p'.price
       ?_ p'.warming.threshold p'.hired Y.χ Y.heat Y.bright (A.symm j).wood (A.symm j).tag, fun j=>(A.symm j).share,fun j => Streak.share_nn _,?_⟩
  · rw [p'.spark.threshold,p'.spark.budget] at hV; exact hV
  exact (Equiv.sum_comp A.symm Streak.share).trans (Streak.full (C.path.levels.blocks i p).branches)
end YM.PhysicalNext.InteractingRank
