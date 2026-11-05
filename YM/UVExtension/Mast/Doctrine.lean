import YM.UVExtension.Lacing.Veranda
import YM.UVExtension.Lacing.Carrier
import YM.UVExtension.Orchard.Racks
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

structure Ability (R:Legato.Bandage Q C W) (m:ℕ)(L:ℕ→Lacing.Banner (A:=O!) («H»:=A.B.a) F (p:=n) m) (u c w a b:ℝ) (v:Keys S) : Prop where -- argument v duplicate? syntax
   plays N : m < N → Lacing.Tribe (A:=O!) («H»:=A.B.a) (p:=n) («F»:=F) m (L N) u c w
   composes N (e:m<N): Pact π (Orchard.Path S v) N n (hol G) W (Orchard.roof S v N n) sT m e (L N)
   owns : Tollgate F u c w a b
   size : (A.B.a.params m).columns≤ a
   fine : 2*w ≤ (A.B.a.params (m+1)).columns

abbrev TopHat (N:ℕ) := Planned.GuardedAtom.Guard.summit F π H N n (Planned.GuardedAtom.Guard.Keeper.sufficient (Vintage.YM.PhysicalNext.Repeat.Graces.Nest.born (housed S v) N n)) (Planned.GuardedAtom.Guard.Keeper.blank (Vintage.YM.PhysicalNext.Repeat.Graces.Nest.born (housed S v) N n)) d

structure Lyrics (r:ℕ) (L:∀ i:ℕ,i<N→ Fence («F»:=F) H N n i (hol G)) (V:μ!) : Prop where
    head : V.tone N=TopHat S v d n N
    earned: Sung π H N n O! W r V
    comes : ∀ i:ℕ,r ≤ i → ∀ hi:i<N, Carol π H N n i (D! N n i hi) (V.tone (i+1)) (V.tone i) (Legato.Bandage.waybill A.B.a i)∧ Chorus H N n i (V.tone i) ∧ ∀ x:(F).Coeff,Lacing.Face H N n (hol G) i (V.tone i) x=Lacing.load H N n (hol G) i (L i hi) (V.tone (i+1)) ((V.tone (i+1)).index x)
end YM.UVExtension.Mast
