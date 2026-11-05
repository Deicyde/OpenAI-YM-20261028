import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Brocade
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Port.Curtain
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Brocade for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Docking
open Function MeasureTheory Lattice Wilson RG Pressure Next.Rank Next.Rank.Perch Tapes
     Spindle Glyph Peak Ac Thirst Corona Value Marker Next.Rank.Station Relation Finset
     Flux RankCovariance Matrix Next.SectorChange Push.SectorMeasure SectorNext.Vacuum
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {i k N p n : ℕ} {ξ : Purse}
    {g : Course C N p k} {B : Binding C} {ht : i<k} {o z : ℝ}
    {P : Rep G (C.S.side (i+1) p)} {R : Rep G (C.S.side i p)}
    (φ : Pole B g ξ ht o z P R) (L : Lantern G (C.path.levels.clock.op i p))

local notation "WX" => ξ.era.coast.Q
local notation "s" => ξ.band
local notation "a" => ξ.horizon
local notation "St" => (C.path.levels.clock.op i p)

set_option quotPrecheck false

variable (X : Points n)
-- reevaluate notation variables
local notation "ID" => (Lane C k ξ.band p ξ.horizon X (show i+1≤k from ht))
local notation "ID0" => (Lane C k ξ.band p ξ.horizon X (show i≤k from ht.le))
local notation "rd" => (readersSky (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i≤k from ht.le).trans g.allow))
local notation "rf" => (readersSky (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i+1≤k from ht).trans g.allow))
local notation "Mar" => ((Ship.yard C ξ.band g.allow p).Cell × Fin n)
local notation "TB" => (Fintype.equivFin (Streak (Lantern.park L))).symm
local notation "hf" => 25 * radiusB (retime XL)+30 ≤ R.p.B
-- appointment on bright shards only
-- earn hs via Teller
variable (hb : 25 * radiusB (retime (Atlas.clim C.path.levels i))+30 ≤ R.p.B)

lemma liftHSky : rd=(C.path.levels.clock.op i p).ratio.parent ∘ rf:= funext (penultimateSky s X g.allow ht)

end YM.PhysicalNext.InteractingRank.Display.Docking
