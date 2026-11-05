import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Trails
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Trails for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Corona Value Glyph Thirst
    MeasureTheory AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid Work.E04
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {N i p k n q d : ℕ} {b : ℝ}
local notation "St" => C.path.levels.clock.op i p
local notation "A" => C.path.levels
local notation "x" => C.path.levels.clock.hatBeta i
local notation "y" => C.path.levels.clock.hatBeta (i+1)

lemma tall_walkSky (h : roomTestSky A b k p d q) (H : i<k) (hp : middleSky A b k ≤ i) (s : Site (C.side (i+1) p)) (j : Bond (C.side (i+1) p)) (hj : j∈parasol s (q*walls y)) :
    separation ((C.path.levels.clock.op i p).ratio.parent s) ((C.path.levels.clock.op i p).ratio.parent j.1) ≤ walls x+8 := by
  have hi := (mem_filter.mp hj).2
  have he : separation s j.1 ≤ q*walls y+8 := (Spindle.doors _).1 hi.1
  let P:= (C.path.levels.clock.op i p).ratio; let v:=P.count.val
  have hz:= foreshorten P s j.1
  have hh : q*walls y+v ≤ walls x*v := h.fresh i hp H; have hv : 0<v := P.count.property
  apply Nat.le_of_mul_le_mul_left _ hv; apply hz.trans
  have ho : 8≤v*8 := Nat.le_mul_of_pos_left _ hv; change _+v≤v*_ ; nlinarith only [he,hh,ho]

variable (X : Points n)

 -- orientation

-- native orientation on BOTH masks and gauges.
variable (ht : k≤N)
lemma risingSky (Y : CellPSky C k b p) (F : Config G (C.side (i+1) p)) (hp : middleSky A b k ≤ i) :
    watchesSky C b p ht (i+1) (hp.trans (Nat.le_succ i)) Y F =
      pull ((Ship.yardSky C b ht p).omega Y) ((C.path.levels.clock.op i p).ratio.embed (spreadCSky C b p ((Station.widerSky ..).trans hp) Y)) F := by
  unfold watchesSky
  rw [spreadCSky, embed_comp (C.S.toDepth ((Station.widerSky ..).trans hp) p) (C.path.levels.clock.op i p).ratio]; rfl
lemma fine_readSky (Y : CellPSky C k b p) (a : Fin n) (h : i<k) (hp : middleSky A b k ≤ i) :
    Peak.readersSky (C:=C) (b:=b) (p:=p) X ht (show i+1≤N from (show i+1≤k from h).trans ht) (Y,a)=
      affine ((Ship.yardSky C b ht p).omega Y) ((C.path.levels.clock.op i p).ratio.embed (spreadCSky C b p ((Station.widerSky ..).trans hp) Y)) (core A X b p (show i+1≤k from h) a) := by
  rw [fillsSky C X b p ht (show i+1≤k from h) ((Station.widerSky ..).trans (hp.trans (Nat.le_succ i))),spreadCSky,embed_comp (C.S.toDepth ((Station.widerSky ..).trans hp) p) (C.path.levels.clock.op i p).ratio]; rfl

end YM.PhysicalNext.InteractingRank
