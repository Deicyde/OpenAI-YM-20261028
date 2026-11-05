import YM.UVExtension.Mast.Doctrine
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} (S:Uses Q hG) (v:Keys S) {C:ℕ→ℝ}{W:Bid.Worth}(R:Legato.Bandage Q C W)
    (d m N n:ℕ)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T'"=> (Orchard.Path S v).levels
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
local notation "V!"=> Voice F H n
local notation "μ!"=> Music F H N n
local notation "sT"=> Legato.Bandage.waybill (A.B.a)

open Eyelet
variable {L:∀ i:ℕ,ℕ → Lacing.Banner («H»:=A.B.a) ((frames G).level d) (p:=n) (A:=hol G) i} {r:ℕ}{u c w a:ℕ→ℝ}
variable (hp:d+3≤ A.B.a.clock.J r)(hx:∀ i:ℕ,r ≤ i→Ability S d n R i (L i) (u i) (c i) (w i) (a i) (a (i+1)) v)

include hp hx
lemma songs (hr:r ≤ N) : ∃ V:μ!, Lyrics S v (W:=W) d N n r (fun i _=>L i N) V:=by
   let h:= Orchard.selected S v; let Z:=TopHat S v d n N; have ht':d ≤ A.B.a.clock.J N:= (le_trans (Nat.le_add_right ..) (hp.trans (A.B.a.fits.mono hr)))
   let hK := Vintage.YM.PhysicalNext.Repeat.Graces.Nest.born (housed S v) N n; let X:= Planned.GuardedAtom.Guard.Keeper.sufficient hK
   have ho : OnTop π H N n O! Z := Vintage.YM.Planned.GuardedAtom.Guard.summon F π H N n X _ h d (sound ..) (Doors.cameras_ge G d) (fun i=> Doors.cameras_holds G d _ i 0) ((R.clock.sequences N d ht').receipts n 0)
   obtain ⟨Y,hY,hp,hX⟩:= Lacing.compose π H N n (hol G) W (L:=fun i _=>L i N) (D:= Orchard.roof S v N n) h (sound ..) R.clock.room R.clock.bank r hr Z ho (Vintage.YM.MergeProof.voice π H N n X _ d h (sound ..) ho) (fun i hi hm=>(hx i hi).composes N hm)
   exact ⟨_,hY,hp,hX⟩
omit hp hx

namespace Lyrics
open Motion
variable {S v d N n}{V :Extra.Histories.Music ((frames G).level d) (Orchard.Path S v) N n} (hV:Lyrics S v (W:=W) d N n r (fun i _=> L i N) V)
-- observer on rebased coordinates. iterative ratios.
local notation "f'"=> terrain H N n O!
include hV
lemma incomeX (i:ℕ)(he:r ≤ i) (hi:i ≤ N) : IsLinearMap ℂ (terrain H N n O! i (V.tone i)) :=by
   have hc:= hV.earned.earned _ he hi; let K:=V.tone i; let T:=(H).rep N n i; let s:= Real.sqrt (T'|>.clock.forcedAllowance i)
   have hk:= Vintage.YM.PhysicalNext.Repeat.Graces.Nest.samples hG (housed S v) N i n hi -- parameters g
   let W':= rowedE K.plays (v:=s) (fun j=> Eligible.mk (Nonempty.intro (Planned.GuardedAtom.Guard.Keeper.sufficient hk)) (hc.earns j).1 ⟨_,(hc.earns j).2⟩) hc.book
   exact ((LinearMap.snd ℂ _ _).comp ((IsLinearMap.mk' _ W').comp K.index.symm.toLinearMap)).isLinear
lemma climbs (i:ℕ)(he:r ≤ i) (hi:i ≤ N)(x:(F).Coeff): ‖terrain H N n O! i (V.tone i) x‖ ≤ (A.B.a.params i).columns*(F).coeffSize ((F).core x):=by
   have hc:= hV.earned.earned _ he hi; let K:=V.tone i; let T:=(H).rep N n i; let s:= Real.sqrt (T'|>.clock.forcedAllowance i)
   have hk:= Vintage.YM.PhysicalNext.Repeat.Graces.Nest.samples hG (housed S v) N i n hi
   let v0:= (V.tone i).index.symm x; obtain ⟨hb,hH⟩:= hc.earns v0
   have he : Eligible (K.plays v0) O! T s:= ⟨⟨Planned.GuardedAtom.Guard.Keeper.sufficient hk⟩,hb,_,hH⟩
   have ht:= hc.cone v0; rw [show K.index v0=x from LinearEquiv.apply_symm_apply ..] at ht -- rw
   change ‖(Eye (K.plays v0) O! T s).2‖ ≤ _; rw [he.vistas]; apply max_le _ _
   · exact (le_add_of_nonneg_right (norm_nonneg _)).trans ((he.costs hH).trans ht)
   exact (le_add_of_nonneg_left (norm_nonneg _)).trans ((he.costs hH).trans ht)
end Lyrics
end YM.UVExtension.Mast
