import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Curtain
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Coordinates
import YM.TraceExtension.Prom.Hill.Memorandum
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Curtain for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Function MeasureTheory Lattice Wilson RG Pressure Next.Rank Next.Rank.Perch Tapes
     Spindle Glyph Peak Ac Thirst Corona Value Marker Next.Rank.Station Relation Finset
     Flux
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {i k N p n a q : ℕ} {ξ : Purse}
    (s : ℝ) (X : Points n) (hN : k≤N) (hp : i<k)

local notation "St" => (C.path.levels.clock.op i p)
set_option quotPrecheck false
local notation "L1" => (Lane C k s p a X (show i+1≤k from hp))
local notation "rd" => (readersSky (C:=C) (b:=s) (p:=p) X hN ((show i≤k from hp.le).trans hN))
local notation "rf" => (readersSky (C:=C) (b:=s) (p:=p) X hN ((show i+1≤k from hp).trans hN))
local notation "Mar" => (Ship.yardSky C s hN p).Cell × Fin n
local notation "prn" => (C.path.levels.clock.op i p).ratio.parent
lemma penultimateSky (j : Mar) : rd j=prn (rf j):= parent_nested (C.path.levels.clock.op i p).ratio (C.S.toDepth (show i+1≤N from (show i+1≤k from hp).trans hN) p) _ (C.S.block_odd _) (C.S.toDepth_odd _ _) _
-- mark extent geometry on any field case

variable {τ : ℝ}

-- parameter before wings costs

section
variable {L : Lantern G (C.path.levels.clock.op i p)}

end
end YM.PhysicalNext.InteractingRank.Display
