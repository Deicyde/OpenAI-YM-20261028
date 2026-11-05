import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Curator
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Survey
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Terrace
/-! # All posts to the Audience lights
same stage-1 Terrace argument with Soft Spear. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Display Display.Docking
open Function MeasureTheory Lattice Wilson RG Pressure Next.Rank Next.Rank.Perch Tapes
     Spindle Glyph Peak Ac Thirst Corona Value Marker Next.Rank.Station Relation Finset
     Flux RankCovariance Matrix Next.SectorChange Push.SectorMeasure SectorNext.Vacuum
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {i k N p n : ℕ} {ξ : Purse}
    {g : Course C N p k} {B : Binding C} {ht : i<k} {o z : ℝ}
    {P : Rep G (C.S.side (i+1) p)} {R : Rep G (C.S.side i p)}
    (φ : Spear B g ξ ht o z P R) (L : Lantern G (C.path.levels.clock.op i p))
local notation "XL" => Atlas.clim C.path.levels i
local notation "XF" => Atlas.clim C.path.levels (i+1)
local notation "WX" => ξ.era.coast.Q
local notation "s" => ξ.band
local notation "a" => ξ.horizon
local notation "St" => (C.path.levels.clock.op i p)
local notation "BT" => tunnel B N i p
set_option quotPrecheck false

variable (X : Points n)
local notation "ID" => (Lane C k ξ.band p ξ.horizon X (show i+1≤k from ht))
local notation "ID0" => (Lane C k ξ.band p ξ.horizon X (show i≤k from ht.le))
local notation "rd" => (readers (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i≤k from ht.le).trans g.allow))
local notation "rf" => (readers (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i+1≤k from ht).trans g.allow))
local notation "Mar" => ((Ship.yard C ξ.band g.allow p).Cell × Fin n)
local notation "TB" => (Fintype.equivFin ((C.path.levels.clock.op i p).Choices)).symm
local notation "hf" => 25 * radiusB (retime XL)+30 ≤ R.p.B
variable (W : (Lane C k ξ.band p ξ.horizon X (show i+1≤k from ht))→ SourceAt G (readers (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i+1≤k from ht).trans g.allow))) (H : principle C P.p g.allow X ξ.band (show i+1≤k from ht) ξ.era.coast.Q ξ.horizon p W) (hF : Boosted (tunnel B N i p) (tell B i) (retime (Atlas.clim C.path.levels i)))
variable (hb : 25 * radiusB (retime (Atlas.clim C.path.levels i))+30 ≤ R.p.B)

local notation "V0" => S_Sunrise φ L X W H hF hb
local notation "HL" => s_haloed φ L X W H hF hb

lemma s_lit_check {w v Q : ℝ} {r : Mar → ℝ} (ht : Spot R V0 lightcast BT w r Q v) (hr : ∀ i,0<r i) (j : ID0) (U : Config G (C.side i p)) (hx : Healthy R.p.threshold (dolmens X s WX R.p.B g.allow (show i≤k from ‹i<k›.le) j.1 j.2.val) U) :
    Ticketed HL (litWord p g.allow s C j.1 j.2.val).val BT U := by
  intro u hu; let q:= flakeTone ∘ HL
  have h₁:hf:= hb
  refine ⟨(old_valid q u (chiseling HL _).1 U).2 (Disjoint.mono_left ?_ hx),?_⟩
  · rw [φ.budget]; exact admitted s X g.allow ‹i<k› HL (s_fringing φ L X W H hF hb) j φ.canvas φ.duty u hu
  intro K
  obtain ⟨v,H1,H2,H3,hβ⟩:= ht.balance
  let A:= nohole St (retime XL) U; let F:= L.park
  have hp: Positioned (retime XL) A U:=rfl
  let f:= stage q u.val A K U; let c:=∏ i∈u.val,v (.inl i); let w:= Poly.toll r (fires q u.val)
  apply Integrable.of_bound ((observer q u).placed _ K|>.atLens hp).aestronglyMeasurable (w⁻¹*c)
  apply Filter.Eventually.of_forall; intro x; change ‖f x‖ ≤ _
  apply le_inv_mul_iff₀ (Poly.worth hr _)|>.2
  change Poly.toll _ _ * ‖stage q _ _ _ _ x‖ ≤ _
  rw [earmark _ u.property.2]; exact Finset.prod_le_prod (fun i _=> stroke_nonneg hr _ _ _ _ _) (fun i _=> H2 (.inl i) _ _ _ _ hp)

-- canonical wiring s picks only HALO leading; pure selection across arbitrary joined tape
section
local notation "hv"=> liftH (ξ:=ξ) X (g:=g) (ht:=ht)
-- actual FULL Flake type, as W pieces plus H insertions. Until Light~Earn.
theorem s_in_stalls {α β ρ : Type} [Fintype α] [Fintype β] [Fintype ρ] {w v Q : ℝ} {r : Mar → ℝ} (Hp : Spot R V0 lightcast BT w r Q v) (hr : ∀ i,0<r i)
    (S : α → Flake St G (retime XL) L.park rd R.p.threshold) (p' : ρ→ Zest G St (retime XL) L.park R.p.threshold) (K : β → Lifted G rf P.p.threshold)
    (hn : n≤2) (he : 30≤ξ.horizon) (ha : Allowed C.path.levels ξ.band k) (hx : Fit C.path.levels ξ.band k X) (m : C.Makes) :
    let J:= Sum.elim S V0; let D:= bequeath (picture P R p' K J hF hb hv) hF; let s':= Glaze P R p' K J hF hb hv sparklers
    (∀ i : Bright D, s' i.val → Slice (sunny D) i (a/3*R.p.B)) ∧
      ∀ (j : ID0) U hh, let T:= litWord p g.allow s C j.1 j.2.val; bed T.val (pitch (Q:=R.p) D s' U)=bed T.val (insertAt j.1 (planters ((φ.approve m X L).tag j U hh) (fun i=> (W (j.1,i)).value))) := by
  intro J D s'; let H':= picture P R p' K J hF hb hv; let Z : ID ↪ α⊕ (ID ⊕ ID) := hatch
  have HH: J ∘ Z=HL:=rfl
  constructor
  · intro i hi
    have hz:i∈ univ.map (wax P R p' K J hF hb hv Z):= (attained P R p' K J hF hb hv Z sparklers hatchling) ▸ (mem_filter.mpr ⟨mem_univ _, hi⟩ : i ∈ (univ.filter (fun z : Bright D=> s' z.val)))
    obtain ⟨u,_,rfl⟩:= mem_map.mp hz
    unfold Slice; unfold D; rw [warmed]
    change ∀ y∈ (fires (flakeTone∘ HL) u.val).val,zone (flakeTone∘ HL) u⊆ _
    intro y hy v hv'
    apply (Spindle.doors _).2; rw [φ.budget]; exact sectors s X g.allow ht HL (s_fringing φ L X W H hF hb) φ.duty φ.canvas hx ha hn he u y hy v hv'
  intro j U h T
  have he :Ticketed HL T.val BT U:= s_lit_check φ L X W H hF hb Hp hr j U h
  exact (congr_arg (bed T.val) (playback P R p' K J hF hb hv Z sparklers hatchling U)).symm.trans (s_foreword φ L X W H hF hb m j U h he)
end
end YM.PhysicalNext.InteractingRank.Soft
