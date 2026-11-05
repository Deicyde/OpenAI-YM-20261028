import YM.MergeProof.North.Freckles
import YM.OPE.Replicas.Price

/-!
# Keep induction facts at n-ary consumption

Strengthening of YM/MergeProof/North/Freckles.lean; most of the proof is
the *same* construction. Adapted from that file, retaining the baseline.
-/
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
private lemma duetPN {Z:ℕ}{E:Rep G (A.B.a.S.side m j)}{R:Rep G (A.B.a.S.side (m+1) j)}(D:GaugeDoor R E)(hk:(Issue.trail Y).rep n j m=E)(h:(Issue.trail Y).rep n j (m+1)=R) {t r u z a b:ℝ} (H':Ribbons.ManyCopies.Unites ((P!).op m j) D Z t r u z a b) : Ribbons.ManyCopies.Unites ((P!).op m j) (duet _ _ _ _ hk h D) Z t r u z a b:=by subst R E; exact H'
include b hm hG
lemma sewedN (Q:ℕ→ℕ) (h : Nest X Y) {D:GaugeDoor ((Issue.trail Y).rep n j (m+1)) ((Issue.trail Y).rep n j m)}
    (hi:Climbs X Y n m j D) (ht:Pungent X.shape A.delay) (hp:Mallow.Tariff (X.target iX iY) L (Q iX) (X.shape.μ iX iY) x0)
    (hξ:100 ≤ (A.B.a.budget (m+1)).supportExponent)(hδ: 100≤(A.B.a.budget m).supportExponent) :
    let c:= A.B.a.clock; let u:=station (c.hatBeta (m+1)); let t:=straw (X.shape.μ (c.J (m+1)) (c.J m)) (P.L (c.J (m+1))) G (c.hatBeta m)
    Ribbons.ManyCopies.Unites ((P!).op m j) D (Q ((P!).J (m+1))) ((K1).supportExponent-4) u ((K0).supportExponent+1/2) ((K0).supportExponent+1) 1 t :=by
   intro c u t; obtain ⟨l,v,Q',U,x,he,hx,rfl⟩:= hi
   have hK:(Q' x.val).p=K1:= (U.knows _ x.property).1.point
   have hE: (U.result x|>.p)=K0:=rfl
   have hv:c.hatBeta (m+1)=Pressure.betaF G x0 L:= (Extra.Iteration.block_beta m).trans (congr_arg (Pressure.betaF _ _) (Extra.Iteration.block_eq A.B.valid m))
   apply duetPN Y _ he hx
   have ht':= Many.vastN hG hm U x (hK.symm ▸ hξ) (hE.symm ▸ hδ) b.r ht (hx ▸ h.samples hG n (m+1) j hm) hp.nonneg hp.shipping
   unfold u; rw [hv]; rw [hK] at ht'; exact ht'
end Bandage
end YM.PhysicalNext.Repeat.Legato
