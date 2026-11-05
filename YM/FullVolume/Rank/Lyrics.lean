import YM.FullVolume.Rank.Setup

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
open Pressure ConnectedActivityE6 Blaze March Lim Umbra FullVolume.Paint
open Matric Guard
namespace Boutique
set_option quotPrecheck false
variable {q:ℕ→ ℕ→∀ p, Shoot.Trail A.B.a p} {f:ℕ→ℕ} {p m:ℕ}
local notation "Z₀"=> (A.B.a.S.oneStep m p).exact_size
local notation "z"=> A.B.a.S.side m p
local notation "Z"=> A.B.a.S.side (m+1) p
local notation "W!"=> A.B.a.clock.op m p
local notation "Q"=> A.B.a.budget m
local notation "t'"=> A.B.a.budget (m+1)
open RG.Shoot Lark Rain Blush
local notation "W₁"=> FullVolume.Urns.layout G Z t'
variable {q':ℕ→ ℕ→∀ p, Shoot.Trail A.B.a p} {g:ℕ→ℕ} (U:Stack X m p q f) (V:Stack X m p q' g)
variable {D:Desk G (A.B.a.S.side m p)}{d:ℕ}{L:ℕ→ℝ} {K':Bid.Worth}
variable (hU:∀ i, (A.B.bake.make (q i)).Selected) (hV:∀ i,(A.B.bake.make (q' i)).Selected) (hd:d+3 ≤ A.B.a.clock.J m)
variable (he:Stationary.Artes.Cadre A.post A.B.kin)(hv:Next.Free.Amplify A.B.M)(hX: Jams.Wild X.shape A.delay)(hh:Lark.Near A m f)(hG':Lark.Near A m g)(ht:Tendsto f atTop atTop)(hl:Tendsto g atTop atTop)
open FullVolume.Shadow
structure Echo (U:Stack X m p q f)(V:Stack X m p q' g): Prop where
   beta : Glints atTop (fun i=> (U i).player.beta) (fun i=> (V i).player.beta)
   rich: Angel (fun n=> (heroB U n).activities.regularOccurrence (A.B.a.budget (m+1))) (fun n=> (heroB V n).activities.regularOccurrence (A.B.a.budget (m+1)))
   earns: Angel (fun n=> (heroB U n).activities.K) (fun n=>(heroB V n).activities.K)
   tips: Angel (G:=G) (c:=z) (fun n=> ((A.B.bake.make (q n)).rep (f n) p m).activities.K) (fun n=> ((A.B.bake.make (q' n)).rep (g n) p m).activities.K)
local notation "φ"=> fun n=> (A.B.bake.make (q n)).rep (f n) p m
local notation "φ'"=> fun n=> (A.B.bake.make (q' n)).rep (g n) p m
variable (hc:Echo U V)(F:∀ i, Cloud (heroB U i))(T:∀ i,Cloud (heroB V i))
structure Voicelet (k:Wing):Prop where
   border : (∀ i,(F i).live.turn=k)∧∀ i,(T i).live.turn=k
   cost : ∃ a:ℝ,(∀ i,(F i).live.weight ≤ a) ∧ ∀ i,(T i).live.weight ≤ a
   reg i: (F i).live.ingredient = (F 0).live.ingredient ∧ (F i).pale.ingredient=(F 0).pale.ingredient
   matchK i: (F i).live.ingredient=(T i).live.ingredient ∧ (F i).pale.ingredient=(T i).pale.ingredient
local notation "B₁"=> Boutique.epoch U
local notation "B₂"=> Boutique.epoch V
local notation "F'"=> panelT U F hh
local notation "T'"=> panelT V T hG'
-- `cost` could be any uniform norm (separate kwargs later).
variable {k:Wing}(hS:Voicelet U V F T k)
include hh hG' hS
lemma voices : Rhyme (K:=B₁) («H»:=B₂) (fun i=>(F' i).live) (fun i=>(T' i).live) k ∧ Rhyme (K:=B₁) («H»:=B₂) (fun i=>(F' i).pale) (fun i=>(T' i).pale) k:=by
   have ht₀ i:= talent (holding U i hh).symm (accordV U F hh i); have ht₁ i:= talent (holding V i hG').symm (accordV V T hG' i)
   obtain ⟨a,hg,hf⟩:= hS.cost; have hB(i): (F' i).live.turn=k:= (ht₀ i).1.symm.trans (hS.border.1 i);have hQ(i):(T' i).live.turn=k:= (ht₁ i).1.symm.trans (hS.border.2 i)
   have hp(i):(F' i).live.weight≤a:= ((ht₀ i).2.1).symm.trans_le (hg i); have hx(i):(T' i).live.weight≤a:= ((ht₁ i).2.1).symm.trans_le (hf i)
   refine ⟨⟨⟨hB,a,hp⟩,⟨hQ,a,hx⟩,fun J hj U=>?_⟩,⟨⟨fun i=>(F' i).together.symm.trans (hB i),a,fun i=>(F' i).rates ▸ hp i⟩,⟨fun i=>(T' i).together.symm.trans (hQ i),a,fun i=>(T' i).rates ▸ hx i⟩,fun J hj U=>?_⟩⟩
   · have he(i):(F' i).live.ingredient=(T' i).live.ingredient:= (ht₀ i).2.2.1.symm.trans ((hS.matchK i).1.trans (ht₁ i).2.2.1);
     simp_rw [he]; exact flowers (x:=0) (b:=a) (Eventually.of_forall fun i=>by rw [dist_zero_right]; exact ((T' i).live.earn ..).trans (hx i)) -- reg unused! remove eventually
   have he(i):(F' i).pale.ingredient=(T' i).pale.ingredient:= (ht₀ i).2.2.2.symm.trans ((hS.matchK i).2.trans (ht₁ i).2.2.2);
   simp_rw [he]; exact flowers (x:=0) (b:=a) (Eventually.of_forall fun i=>by rw [dist_zero_right]; exact ((T' i).pale.earn ..).trans ((T' i).rates ▸ hx i))
local notation "θ"=> A.B.a.clock.J (m+1)
local notation "δ"=> A.B.a.clock.J m
local notation "u"=> ((P.L θ).val:ℝ)^d
local notation "γ"=> fun i=> A.B.kin.alpha (f i) m
local notation "δ'"=>fun i=> A.B.kin.alpha (g i) m
local notation "Π₁"=>fun n=>Cub.innerT (U n).stock center (F n) (d:=d)
local notation "Π₂"=>fun n=>Cub.innerT (V n).stock center (T n) (d:=d)
local notation "s₁"=>fun n=>Blush.scope (U n).sale (F n) 0
local notation "s₂"=>fun n=>Blush.scope (V n).sale (T n) 0
set_option quotPrecheck false
variable (hθ:∀ i,Cub.Tyne (U i).stock center (q i) (F i) d)(hθ':∀ i,Cub.Tyne (V i).stock center (q' i) (T i) d)
include hU hV he hv hX ht hl hθ hθ' hc hG
local notation "v"=>Rain.lint X.target A m
local notation "w"=>Trio.base v (Pressure.radiusB (A.B.a.clock.hatBeta m))
open ConnectedActivityE6.Lim.Umbra
set_option maxHeartbeats 520000 in
lemma micro: (∀ i,s₁ i=s₁ 0) ∧ (∀ i,s₂ i=s₁ 0)∧ SeatE (fun i=>(Π₁ i).bulk) (fun i=>(Π₂ i).bulk) Q (s₁ 0) ∧ FullVolume.Paint.Credit (fun i=> (Π₁ i).forced) (fun i=>(Π₂ i).forced):=by
    let I:= Boutique.loop U hh;let D:= Boutique.loop V hG'; obtain ⟨XK,hp⟩:= quarters hX m; let c(n):= deposits X XK hp (U n).player (P:=Z₀) (Lark.seats m _ _ (f n) (hh n).2 (U n).player) (hh n).1 X.pledging.conducts.full (I n); let c'(n):=deposits X XK hp (V n).player (P:=Z₀) (Lark.seats m _ _ (g n) (hG' n).2 (V n).player) (hG' n).1 X.pledging.conducts.full (D n) -- P param not Z
    have hf:=Roof.coating X.pledging.conducts (U 0|>.hx) (R:=fun _=>(U 0).player) (s:= Set.univ) (fun _ _=> (hU 0|>.represents _ _ _ (U 0).hx).band)
    let Ξ i:= (U i).ask; let Θ i:=(V i).ask; let f₀ i:= (U i).stock.ordinal; let f₁ i:= (V i).stock.ordinal
    have ha:= allies he hv ht hl hh hG' hf.decent Z₀ W₁ (heroB U) (heroB V) (fun i=>holding U i hh) (fun i=>holding V i hG') hc.rich hc.earns hc.beta
    have h₀ :Tendsto f₀ atTop atTop:= tendsto_atTop_mono (f:=f) (fun i=> (U i).pays) ht; have h₁ : Tendsto f₁ atTop atTop:= tendsto_atTop_mono (f:=g) (fun i=> (V i).pays) hl
    have he' (s):= swaths X he hv ht hl hh hG' hf.decent hX (fun i=>(U i).stock.W) (fun i=>(V i).stock.W) h₀ h₁ Ξ Θ hc.beta X.pledging.conducts.full s
    obtain ⟨hA,hQ⟩:= voices U V hh hG' F T hS -- order
    have hD i:= plates U F hh i (↑(u:ℝ)); have hD' i:=plates V T hG' i (↑(u:ℝ))
    have hd i: (Π₁ i).bulk=Blush.fields (I i) (F' i) ↑(u:ℝ):=by rw [(hD i).2.2.2,Complex.ofReal_pow,Complex.ofReal_natCast]; rfl -- I unfolding
    have hd' i: (Π₂ i).bulk=Blush.fields (D i) (T' i) ↑(u:ℝ):=by rw [(hD' i).2.2.2,Complex.ofReal_pow,Complex.ofReal_natCast];rfl
    have hM i: (φ i).p=A.B.a.budget m:= hU i|>.represents (f i) p m ((U i).hx.le)|>.vac -- notation syntax
    have hM' i: (φ' i).p=A.B.a.budget m:= hV i|>.represents (g i) p m ((V i).hx.le)|>.vac
    have H₀ i j:(A.B.a.budget m).Regular (Blush.scope (I i) (F' i) 0 j) (Blush.fields (I i) (F' i) ↑(u:ℝ) j):=by rw [← hd,show Blush.scope (I i) (F' i) 0= s₁ i from (hD i).2.2.1]; exact hM i ▸ (hθ i).format.regular j
    have H₁ i j:(A.B.a.budget m).Regular (Blush.scope (D i) (T' i) 0 j) (Blush.fields (D i) (T' i) ↑(u:ℝ) j):=by rw [← hd',show Blush.scope (D i) (T' i) 0= s₂ i from (hD' i).2.2.1]; exact hM' i ▸ (hθ' i).format.regular j
    obtain ⟨hU',hT',hE⟩:= Umbra.spanV I D c c' ha.mirror F' T' (u:ℝ) (by positivity) hA hQ ha.fore ha.tail rfl ((Rain.jersey (A:=A) (m:=m)).1.le) H₀ H₁ (fun i=> (hD 0|>.2.2.1).symm ▸ (hθ 0).format.origin i)
    refine ⟨fun i=>(hD i).2.2.1.symm.trans ((hU' i).trans (hD 0).2.2.1),fun i=> (hD' i).2.2.1.symm.trans ((hT' i).trans (hD 0).2.2.1),?_,?_⟩
    · dsimp only; simp_rw [hd,hd']; exact (hD 0).2.2.1 ▸ hE
    have hz: (Q).order ≤ (M.p.profile δ).order:=(Rain.jersey (A:=A) (m:=m)).1.le
    have hx := backdrop I D c c' ha rfl hz h₀ h₁ (Rain.screens X.target A m) he' («z»:=w) (by unfold Trio.base; omega) (Lark.nearby hh) (Lark.nearby hG') hf.width hG hA
    have hx' := backdrop I D c c' ha rfl hz h₀ h₁ (Rain.screens X.target A m) he' («z»:=w) (by unfold Trio.base; omega) (Lark.nearby hh) (Lark.nearby hG') hf.width hG hQ
    have hc : Jade (fun i=>pupil (U i).stock center (F i).live) (fun i=>pupil (V i).stock center (T i).live):=by simp_rw [← (fun i=> (hD i).1),← (fun i=> (hD' i).1)]; exact hx
    have hp : Jade (fun i=>pupil (U i).stock center (F i).pale) (fun i=>pupil (V i).stock center (T i).pale):=by simp_rw [← (fun i=> (hD i).2.1),← (fun i=> (hD' i).2.1)]; exact hx'
    exact ((FullVolume.Paint.Credit.castC hc.cusp).sum (FullVolume.Paint.Credit.castC hp.cusp|>.scal Complex.I)).scal (((P.L θ).val:ℂ)^d) -- order
end Boutique
end Bandage
end YM.PhysicalNext.Repeat.Legato
