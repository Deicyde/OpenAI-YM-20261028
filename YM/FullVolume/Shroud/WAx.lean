import YM.FullVolume.Shroud.Vigil
import YM.MergeProof.Escarp
import YM.MergeProof.Revenue
import YM.MergeProof.Tanger
import YM.MergeProof.Temper



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

variable {q:ℕ→∀ p,Shoot.Trail A.B.a p}
local notation "H!"=> A.B.bake.make q
private lemma duet_Pt {R:RG.Rep G (A.B.a.S.side m j)}{E:RG.Rep G (A.B.a.S.side (m+1) j)}{D:GaugeDoor E R}{a c d k t u:ℝ}{K:ℕ}
    (he:(A.B.bake.make q).rep n j (m+1)=E) (h:(A.B.bake.make q).rep n j m=R) (hp: Volant ((P!).op m j) D K a c d k t u): Volant ((P!).op m j) (duet (A.B.bake.make q) n j m h he D) K a c d k t u:= by subst E R; exact hp
-- Supply.Enter stages asks travel and Duty
variable (Q:ℕ→ℕ)
include b hm hG
lemma glassDoor (U_:Boutique X q n j m) (ht:Pungent X.shape A.delay) (hp:Mallow.Tariff (X.target iX iY) L (Q iX) (X.shape.μ iX iY) x0)
    (hξ:100 ≤ (A.B.a.budget (m+1)).supportExponent)(hδ: 100≤(A.B.a.budget m).supportExponent) :
    let c:= A.B.a.clock; let u:=station (c.hatBeta (m+1)); let t:=straw (X.shape.μ (c.J (m+1)) (c.J m)) (P.L (c.J (m+1))) G (c.hatBeta m)
    Volant ((P!).op m j) U_.gate (Q ((P!).J (m+1))) ((K1).supportExponent-4) u ((K0).supportExponent+1/2) ((K0).supportExponent+1) 1 t ∧
       Accent.Duty (A.B.bake.make q) (fun i=>Q ((P!).J (i+1))) m (probe x1) u t:=by
   intro c u t; let U:=U_.stock; let Q':=fun _:ℝ=> (A.B.bake.make q|>.rep n j (m+1)); let x:= Boutique.center; have he : (A.B.bake.make q).rep n j m=U.result x:= U_.taught
   have hK:(Q' x.val).p=K1:= (U.knows _ x.property).1.point
   have hE: (U.result x|>.p)=K0:=rfl
   have hv:c.hatBeta (m+1)=Pressure.betaF G x0 L:= (Extra.Iteration.block_beta m).trans (congr_arg (Pressure.betaF _ _) (Extra.Iteration.block_eq A.B.valid m))
   let p':= probe x1
   refine ⟨?_,⟨⟨?_,?_⟩,⟨hδ,hξ⟩,?_,?_,?_⟩⟩
   · apply duet_Pt (q:=q) (show _ = Q' x from rfl) he
     have ht := Many.ripe hG hm U x (hK.symm ▸ hξ) (hE.symm ▸ hδ) b.r ht U_.up hp.nonneg hp.shipping
     unfold u; rw [hv]; rw [hK] at ht; exact ht
   · rw [hv]; exact hp.probeT
   · rw [hv]; exact hp.small
   · let q := Q iX; have he' : (K1).B=Pressure.radiusB x1:=rfl
     change let T:= q*Extra.Multi.siteFactor ((K1).B)*p'+4*p'; T+Real.exp T*T ≤ u
     unfold p' u; rw [he', hv]; exact hp.buy
   · change (((K0).B+(K0).B+1:ℕ):ℝ)^4*(t+(Q iX)*Extra.Multi.siteFactor ((K0).B)*probe x1)≤1/2; rw [hv]; exact hp.lodging
   change Real.exp (t+(Q iX)*Extra.Multi.siteFactor ((K0).B)*probe x1)-1 ≤ 1; rw [hv]; exact hp.credits
end Bandage
end YM.PhysicalNext.Repeat.Legato
