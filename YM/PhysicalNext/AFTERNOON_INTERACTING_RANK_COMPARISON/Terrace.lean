import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Brocade

/-!
# Supply the lit hypothesis in Audience

Here for the one- and two-marker Rank requests with arbitrary
copies. Requires the `principle` exactly on each probe. No assertion
there is a ready pencil or that some independently chosen Rep could
produce these. This calculation is independent of commitments for
the non-leading pieces: it links the actual *chosen mark representation*
to its `planters` on the same Ignition.
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
local notation "XL" => Atlas.clim C.path.levels i
local notation "XF" => Atlas.clim C.path.levels (i+1)
local notation "WX" => ξ.era.coast.Q
local notation "s" => ξ.band
local notation "a" => ξ.horizon
local notation "St" => (C.path.levels.clock.op i p)
local notation "BT" => tunnel B N i p
set_option quotPrecheck false

variable (X : Points n)
-- reevaluate notation variables
local notation "ID" => (Lane C k ξ.band p ξ.horizon X (show i+1≤k from ht))
local notation "ID0" => (Lane C k ξ.band p ξ.horizon X (show i≤k from ht.le))
local notation "rd" => (readers (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i≤k from ht.le).trans g.allow))
local notation "rf" => (readers (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i+1≤k from ht).trans g.allow))
local notation "Mar" => ((Ship.yard C ξ.band g.allow p).Cell × Fin n)
local notation "TB" => (Fintype.equivFin ((C.path.levels.clock.op i p).Choices)).symm
local notation "hf" => 25 * radiusB (retime XL)+30 ≤ R.p.B
-- appointment on bright shards only
variable (W : (Lane C k ξ.band p ξ.horizon X (show i+1≤k from ht))→ SourceAt G (readers (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i+1≤k from ht).trans g.allow))) (H : principle C P.p g.allow X ξ.band (show i+1≤k from ht) ξ.era.coast.Q ξ.horizon p W) (hF : Boosted (tunnel B N i p) (tell B i) (retime (Atlas.clim C.path.levels i)))
-- earn hs via Teller
variable (hb : 25 * radiusB (retime (Atlas.clim C.path.levels i))+30 ≤ R.p.B)

local notation "V0" => Sunrise φ L X W H hF hb
local notation "HL" => haloed φ L X W H hF hb

-- Legend purchased by Spot on PURE alone.


-- canonical wiring s picks only HALO leading; pure selection across arbitrary joined tape
section
local notation "hv"=> liftH (ξ:=ξ) X (g:=g) (ht:=ht)
omit φ in
def hatch {α V : Type} : V↪ α⊕ (V⊕ V):= Embedding.inl.trans Embedding.inr
def sparklers {α V : Type} (i : α ⊕ (V ⊕ V)) : Prop := Sum.elim (fun _=>False) lightcast i
lemma hatchling {α V : Type} (i : α ⊕ (V ⊕ V)) : sparklers i ↔ i∈Set.range hatch:= by
  constructor
  · rintro h; rcases i with i|(i|i); exact False.elim h; exact ⟨_,rfl⟩; exact False.elim h
  rintro ⟨v,rfl⟩; trivial
-- actual FULL Flake type, as W pieces plus H insertions. Until Light~Earn.

end
end YM.PhysicalNext.InteractingRank.Display.Docking
