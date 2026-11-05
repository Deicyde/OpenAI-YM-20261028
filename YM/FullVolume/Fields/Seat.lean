import YM.FullVolume.Fields.Eves
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}(hG:G.Simple){M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:Bolt A}{C:ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K)
open YM.MergeProof MergeProof.Matric Guard
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Sever
variable {q:ℕ→ℕ→∀ p,Shoot.Trail A.B.a p}{f:ℕ→ℕ}{p k :ℕ}(J:Rising X q f p k) {ψ:ℕ→ℕ} (T:∀ n d N p,TransferData ((Labels.frames G).level d) (A.B.bake.make (q n)) N p)
variable (hx:Jams.Wild X.shape A.delay)(hz:Nest X Y)
namespace Rising
open Marker
open MergeProof.Accent Extra.Multi Extraction Extraction.Lease
set_option quotPrecheck false
local notation "P'"=> A.B.a
local notation "F'"=> (Labels.frames G).level
local notation "C'"=> fun i=> wen (A:=A) q ψ T i
variable {D:∀ n N p m:ℕ,m<N→GaugeDoor ((A.B.bake.make (q n)).rep N p (m+1)) ((A.B.bake.make (q n)).rep N p m)} {u π φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{p':ℕ→ℕ}
variable (hh:∀ᶠ r in atTop,∀ᶠ n in atTop, Ponds (wen (A:=A) q ψ T n) K u π φ δ ζ p' (D n) p r (f n))(hp:∀ d,∀ᶠ i in atTop,0<ζ d i)(ht:∀ i,1 ≤ p' i)
variable {n:ℕ}(v:Fin n→ℕ)(z:∀ i:Fin n,((Labels.frames G).level (v i)).Coeff)
abbrev robe (A: Levels G)(p:ℕ) (e:Points n)(m:ℕ): Fin n→ Site (A.S.side m p):= wrap _ ∘ Extraction.address (A.S.a m) e
local notation "U'"=> Stock.census
lemma absolute {G:Gauge}(p N:ℕ)(C:Family G)(v:Fin n→ℕ)(z: ∀ i:Fin n,C.label (v i))(a:∀ m,Fin n→ Site (C.S.side m p))(i:(Stock.census (Fin n)).Mode)(hi:i.val=Finset.univ): pilot C v z p N a (fun _=>(1,false)) i= C.numeric N p (fun i=>⟨v i,z i⟩) (a N):=by
    have he(i:Fin n):seed C v z p N a (fun _=>(1,false)) i=C.O N p (z i) (a N i):=by funext U; unfold seed item stepUp; dsimp only; rw [pull_one]; change C.O N p (z i) 0 (Lattice.translate _ U)=_; rw [C.translation 0,zero_add]
    unfold pilot; simp_rw [hi,he]; rfl
variable (hc:∀ i,Tenable b J T hz (v i) ψ)(x:Points n)(h: x∈ NoHit A.B.a.S p n)(he:Eves.ancestor A.B.a.S x)
local notation "o"=> robe P' p x
include hG b hx hz J T hh hp ht hc he h
set_option maxHeartbeats 480000 in
lemma cinema : CauchySeq fun i=> (C' i).numeric (f i) p (fun k=>⟨v k,z k⟩) (o (f i)):=by
    obtain ⟨r,hr⟩:= eventually_atTop.mp ((hh.and (Eves.positions P' x h he hG)).and ((Eves.lateAnch P' x he).and ((eventually_ge_atTop k).and ((eventually_all.mpr fun i=> hp (v i)).and (eventually_all.mpr fun i=>eventually_ge_atTop (ψ (v i)))))))
    have hM(n):Migrating (A.B.bake.make (q n)) r p (f n) (o):= ⟨fun i hi _=> Eves.turns P' i x (hr i hi|>.2.1)⟩; let B:= Stock.census (Fin n)
    have hp' j(h:j≥ r)(i k:Fin n)(hu:i≠k):(P'|>.budget j|>.B)^2 ≤ separation (o j i) (o j k):= hr j h |>.1.2 i k hu
    have hg: Function.Injective (o r):=by intro i j H; by_contra hh; have hi:= hp' r le_rfl _ _ hh; rw [H,separation_self] at hi; exact (Nat.not_le.mpr (Nat.pow_pos ((A.B.a.budget r).B_pos))) hi
    let pᵢ:= Stock.final (Fin n)
    have hm:= J.arrives hG b T hx hz v z B hc (o) (fun _=>(1,false)) (hr r le_rfl|>.2.2.2.2) (hr r le_rfl|>.1.1) (hr r le_rfl|>.2.2.2.1) hM (p':=p') (show Occupancy (o r) (p' r) from fun i=> (Occupancy.of_injective hg i).trans (ht r)) (fun j hj=> ⟨fun i h n _ v _=> hp' j hj n v⟩) (hr r le_rfl|>.2.2.1) pᵢ
    exact cauchy_copy hm (Eventually.of_forall fun i=> absolute p (f i) (C' i) v z (o) pᵢ rfl)
end Rising
end YM.PhysicalNext.Repeat.Legato.Bandage
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Rising.cinema
