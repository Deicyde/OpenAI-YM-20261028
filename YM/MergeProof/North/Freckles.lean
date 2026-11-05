import YM.MergeProof.Escarp
import YM.MergeProof.North.Afire
import YM.MergeProof.North.Morsel
import YM.MergeProof.North.Price
import YM.MergeProof.North.Shasta
import YM.MergeProof.Revenue







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
open MergeProof Accent Menu
variable {K':ℕ→ℕ→ℕ}{μ:ℕ→ℕ→ℕ}
local notation "T0"=>Issue.trail Y
local notation "P0"=> A.B.a
local notation "P!"=> A.B.a.clock
set_option quotPrecheck false
variable {j n m:ℕ}(hm:m<n)
local notation "iY"=> (P!).J m
local notation "iX"=> (P!).J (m+1)
local notation "L"=> P.L iX
local notation "x0"=> (P!).hatBeta m
local notation "x1"=> (P!).hatBeta (m+1)
local notation "K0"=> (P0).budget m
local notation "K1"=> (P0).budget (m+1)

local notation "F'"=> hol G
private lemma duetS {E:Rep G (A.B.a.S.side m j)} {Z:Rep G (A.B.a.S.side (m+1) j)}(D:GaugeDoor Z E)(hk:(Issue.trail Y).rep n j m=E)(h:(Issue.trail Y).rep n j (m+1)=Z)(u:ℝ)(hp:MergeProof.Float.Runs D ((P!).op m j) u): MergeProof.Float.Runs (duet (Issue.trail Y) n j m hk h D) ((P!).op m j) u:=by subst E Z; exact hp
private lemma duetF {E:Rep G (A.B.a.S.side m j)} {Z:Rep G (A.B.a.S.side (m+1) j)}(D:GaugeDoor Z E)(hk:(Issue.trail Y).rep n j m=E)(h:(Issue.trail Y).rep n j (m+1)=Z)(d:ℕ)(u:ℝ) (hp:∀ (q:Set Wing)(M:Lotus.Leaf Z), M.turn∈q → 0∈ M.crest→ MergeProof.Coupon (localSection G d) (Issue.trail Y) n j m (hol G) (MergeProof.prose M) (entry M) 0 (duet _ _ _ _ hk h D) q (Complex.ofReal ∘ M.cicada) 0 (u*load M) (u*load M) (2*load M)) : MergeProof.Throws (Issue.trail Y) n j m (duet _ _ _ _ hk h D) F' (localSection G d) u :=by subst E Z; exact hp
private lemma duetP {Z:ℕ}{E:Rep G (A.B.a.S.side m j)}{R:Rep G (A.B.a.S.side (m+1) j)}(D:GaugeDoor R E)(hk:(Issue.trail Y).rep n j m=E)(h:(Issue.trail Y).rep n j (m+1)=R) {t r u z a b:ℝ} (H':Ribbons.Unites ((P!).op m j) D Z t r u z a b) : Ribbons.Unites ((P!).op m j) (duet _ _ _ _ hk h D) Z t r u z a b:=by subst R E; exact H'
lemma wise {v:Side}(Yq:RG.Rep G v)(hs:HasSlots Yq.p Yq.activities):Arsenal Yq:=by
   let A:=Yq.activities; constructor
   · rintro p ⟨v,hv⟩; let i:= Blush.found v p hv; refine ⟨i,?_,hs.regular _⟩; rw [show (Yq.activities.reg i)= _ from Blush.latch Yq v p hv hs]
   intro p hp; let w0:=Planned.GuardedAtom.Guard.Keeper.sufficient hs; let b: Extra.Histories.StockTag _:= ⟨p,hp.1,hp.2⟩; let q:= w0.code (b,0); refine ⟨q,cardK w0 b,fun U he=> ?_⟩
   have ht : (A.forced q).support∩RG.flags Yq.p.threshold U=(A.forced q).inventory:= by
      have hxx: barcode A q=p:= cardK w0 b; rw [Prod.mk.inj hxx|>.1,Prod.mk.inj hxx|>.2,he]
   exact ⟨ht,w0.pass _ _ ht⟩
include b hm hG
lemma thaw (h : Nest X Y) {D:GaugeDoor ((Issue.trail Y).rep n j (m+1)) ((Issue.trail Y).rep n j m)} (hi:Climbs X Y n m j D)(d:ℕ)(hd:d+3≤ iY) (hc:Real.exp (Release.base ((M.p.profile iY).supportExponent+2) (X.span iX iY)) ≤ (L).val)
    (u:ℝ)(hs: let «P»:= M.p.profile iY; (coinFee G «P» d L+|2*((L).val:ℝ)^d*(Mercury.volt x0 «P».order «P».power*((X.target iX iY).goal L x0)⁻¹)|)* Graces.host G «P» d≤ u):
    MergeProof.Float.Runs D ((P!).op m j) (6*((L).val:ℝ))∧ Throws (Issue.trail Y) n j m D F' (localSection G d) u:= by
   obtain ⟨l,v,Q,U,x,he,hx,rfl⟩:=hi
   refine ⟨duetS _ _ he hx _ (Many.warm hG hm U x b.r (wise _ ?_) ?_ hc b.stamp),duetF Y _ he hx _ u fun q V hV hq=> Graces.respects hG hm h b.r U x he hx b.clock b.stamp ?_ V u hs q hV hq⟩
   · have hp:= h.samples hG n m j hm.le; rw [he] at hp; exact hp
   · have he:= Graces.feet hd b.clock; exact b.tunes _ _ _ he _ (P.large _).need |>.1
   omega
lemma sewed (Q:ℕ→ℕ) (h : Nest X Y) {D:GaugeDoor ((Issue.trail Y).rep n j (m+1)) ((Issue.trail Y).rep n j m)}
    (hi:Climbs X Y n m j D) (ht:Pungent X.shape A.delay) (hp:Mallow.Tariff (X.target iX iY) L (Q iX) (X.shape.μ iX iY) x0)
    (hξ:100 ≤ (A.B.a.budget (m+1)).supportExponent)(hδ: 100≤(A.B.a.budget m).supportExponent) :
    let c:= A.B.a.clock; let u:=station (c.hatBeta (m+1)); let t:=straw (X.shape.μ (c.J (m+1)) (c.J m)) (P.L (c.J (m+1))) G (c.hatBeta m)
    Ribbons.Unites ((P!).op m j) D (Q ((P!).J (m+1))) ((K1).supportExponent-4) u ((K0).supportExponent+1/2) ((K0).supportExponent+1) 1 t :=by
   intro c u t; obtain ⟨l,v,Q',U,x,he,hx,rfl⟩:= hi
   have hK:(Q' x.val).p=K1:= (U.knows _ x.property).1.point
   have hE: (U.result x|>.p)=K0:=rfl
   have hv:c.hatBeta (m+1)=Pressure.betaF G x0 L:= (Extra.Iteration.block_beta m).trans (congr_arg (Pressure.betaF _ _) (Extra.Iteration.block_eq A.B.valid m))
   apply duetP Y _ he hx
   have ht':= Many.vast hG hm U x (hK.symm ▸ hξ) (hE.symm ▸ hδ) b.r ht (hx ▸ h.samples hG n (m+1) j hm) hp.nonneg hp.shipping
   unfold u; rw [hv]; rw [hK] at ht'; exact ht'
end Bandage
end YM.PhysicalNext.Repeat.Legato
