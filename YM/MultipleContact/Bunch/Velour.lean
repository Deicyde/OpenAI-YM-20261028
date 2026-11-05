import YM.MultipleContact.Bunch.Price
import YM.MergeProof.North.Bonus
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
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
private lemma bunch_duet {Z:ℕ}{E:Rep G (A.B.a.S.side m j)}{R:Rep G (A.B.a.S.side (m+1) j)}(D:GaugeDoor R E)(hk:(Issue.trail Y).rep n j m=E)(h:(Issue.trail Y).rep n j (m+1)=R) {t r u z a b:ℝ} (H':YM.MergeProof.BatchRibbons.Unites (slot:=slot) ((P!).op m j) D Z t r u z a b) : YM.MergeProof.BatchRibbons.Unites (slot:=slot) ((P!).op m j) (duet _ _ _ _ hk h D) Z t r u z a b:=by subst R E; exact H'
include b hm hG
lemma packet_lease (Q:ℕ→ℕ) (h : Nest X Y) {D:GaugeDoor ((Issue.trail Y).rep n j (m+1)) ((Issue.trail Y).rep n j m)}
    (hi:Climbs X Y n m j D) (ht:Pungent X.shape A.delay) (hp:Mallow.Tariff (X.target iX iY) L (Q iX) (X.shape.μ iX iY) x0)
    (hξ:100 ≤ (A.B.a.budget (m+1)).supportExponent)(hδ: 100≤(A.B.a.budget m).supportExponent) :
    let c:= A.B.a.clock; let u:=station (c.hatBeta (m+1)); let t:=straw (X.shape.μ (c.J (m+1)) (c.J m)) (P.L (c.J (m+1))) G (c.hatBeta m)
    YM.MergeProof.BatchRibbons.Unites (slot:=slot) ((P!).op m j) D (Q ((P!).J (m+1))) ((K1).supportExponent-4) u ((K0).supportExponent+1/2) ((K0).supportExponent+1) 1 t :=by
   intro c u t; obtain ⟨l,v,Q',U,x,he,hx,rfl⟩:= hi
   have hK:(Q' x.val).p=K1:= (U.knows _ x.property).1.point
   have hE: (U.result x|>.p)=K0:=rfl
   have hv:c.hatBeta (m+1)=Pressure.betaF G x0 L:= (Extra.Iteration.block_beta m).trans (congr_arg (Pressure.betaF _ _) (Extra.Iteration.block_eq A.B.valid m))
   apply bunch_duet (slot:=slot) Y _ he hx
   have ht':= Many.Bunch.vast (slot:=slot) hG hm U x (hK.symm ▸ hξ) (hE.symm ▸ hδ) b.r ht (hx ▸ h.samples hG n (m+1) j hm) hp.nonneg hp.shipping
   unfold u; rw [hv]; rw [hK] at ht'; exact ht'
end Bandage
end YM.PhysicalNext.Repeat.Legato

namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft Mallow
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent

variable (hG:G.Simple) {M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{K:ℕ→ℝ}{W:Bid.Worth}(b:Bandage X K W)(Y:Bolt A)(Q:ℕ→ℕ)
variable (t:ℕ→ℕ)(Z:∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p)(D:∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail Y).rep N p (m+1)) ((Issue.trail Y).rep N p m))
structure Broader (S:Family G)(δ:ℕ→ℝ)(r:ℕ→ℕ) (D:∀ N p m:ℕ,m<N→GaugeDoor (S.path.rep N p (m+1)) (S.path.rep N p m)) : Prop where
   mother : ∃ χ:ℕ→ℝ,(∀ i,0≤χ i) ∧ ∀ d:ℕ,Ribbons.Wares S (μ:=D) (δ:=δ) (r:=r) (S.ref d) d χ δ (bling S.path.levels) ∧ ∃ p:ℕ→ℝ,∀ i, S.ref d ≤ i → Duty S.path r i (δ i) (p i) (χ i) ∧ ∀ (N n : ℕ)(h : i < N), MergeProof.Menu.Volant (S.path.levels.clock.op i n) (D N n i h) (r i) ((S.path.levels.budget (i+1)).supportExponent-4) (p i) ((S.path.levels.budget i).supportExponent+1/2) ((S.path.levels.budget i).supportExponent+1) 1 (χ i) ∧ ∀ (α: Type) [_hα:Fintype α] [_hd: DecidableEq α] [_hi: Inhabited α], BatchRibbons.Unites (slot:=α) (S.path.levels.clock.op i n) (D N n i h) (r i) ((S.path.levels.budget (i+1)).supportExponent-4) (p i) ((S.path.levels.budget i).supportExponent+1/2) ((S.path.levels.budget i).supportExponent+1) 1 (χ i)
set_option quotPrecheck false
local notation "C"=> Family.mk (Issue.trail Y) (hol G) (Labels.frames G) (localSection G) t Z
local notation "U"=>A.B.a.budget
local notation "J"=> A.B.a.clock.J
local notation "x"=> A.B.a.clock.hatBeta
variable (hN:Chateau b Q Y t Z D)(ht:∀ m:ℕ,100 ≤ (A.B.a.budget m).supportExponent)
include hN hG ht
lemma obtains_broader (hv:Mallow.AccordV X.shape Q A.delay) (hV :∀ i j,StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) : Broader C (renal A.B.a) (mutt A.B.a Q) D:=by
   let y m:= Mallow.straw (X.shape.μ (J (m+1)) (J m)) (P.L (J (m+1))) G (x m)
   let o m:= station (x (m+1)); have h(i): x (i+1)=Pressure.betaF G (x i) (P.L (J (i+1))):= by rw [Extra.Iteration.block_beta,Extra.Iteration.block_eq A.B.valid]
   have hA(d i:ℕ)(hi:t d ≤ i): d+3≤ J i:= (hN.opens d).trans (A.B.a.fits.mono hi)
   have hm(i j:ℕ)(hi:j ≤ J i) := hv _ _ (A.B.valid.pays i) _ (step_paid _ _) j hi
   have hf(N p m:ℕ)(hp:m<N):= paneer hG b Y hp Q hN.nest (hN.motion N m p hp) hN.wall.hold (hN.wall.word _ _ (A.B.valid.pays m) _ (step_paid _ _)) (ht _) (ht m)
   refine ⟨y,(by intro i; unfold y straw lauge; positivity),fun d=> ?_⟩
   constructor
   · refine ⟨⟨o,⟨fun N p i he h=>⟨(hf N p i h).1,sewed hG b Y h Q hN.nest (hN.motion N i p h) hN.wall.hold (hN.wall.word _ _ (A.B.valid.pays i) _ (step_paid _ _)) (ht _) (ht _)⟩,fun i _=>(hf (i+1) 0 i i.lt_succ_self).2⟩⟩,fun i _=> (hm i 0 (Nat.zero_le _)).2.2.1,fun i _=> (hf (i+1) 0 i i.lt_succ_self).2.hats,fun i _=>?_,fun i _=>Real.one_le_exp (Real.sqrt_nonneg _),fun i ho N p he=>?_⟩
     · let I:= M.p.profile (J i); have hz: (U i).supportExponent= I.supportExponent:=congr_arg Stage.supportExponent (params_eq A.B.valid _)
       change (((U i).B+(U i).B+1:ℕ):ℝ)^4*Ribbons.scurry A.B.a (mutt A.B.a Q) y (renal A.B.a i) i ≤1/2 ∧ Real.exp (Ribbons.scurry A.B.a (mutt A.B.a Q) y (renal A.B.a i) i)-1 ≤1; unfold Ribbons.scurry renal; rw [hz,h i]; exact ⟨(hm i 0 (Nat.zero_le _)).1,(hm i 0 (Nat.zero_le _)).2.1⟩
     let D:= J i; have hx:=hA d i ho; change MergeProof.Float.Runs _ (A.B.a.clock.op i p) (6*((A.B.a.S.block i).val:ℝ))∧ MergeProof.Throws _ _ _ i _ _ _ (bling A.B.a i)
     rw [Extra.Iteration.block_eq A.B.valid]; apply thaw hG b Y he hN.nest (hN.motion _ _ _ he) d hx (hV _ _ (step_paid _ _)); unfold bling; rw [h i]; exact (hm i d (le_trans (Nat.le_add_right ..) hx)).2.2.2.2
   exact ⟨o,fun i _=>⟨(hf (i+1) 0 i i.lt_succ_self).2,fun N p he=>⟨(hf N p i he).1,fun slot _ _ _=>packet_lease (slot:=slot) hG b Y he Q hN.nest (hN.motion N i p he) hN.wall.hold (hN.wall.word _ _ (A.B.valid.pays i) _ (step_paid _ _)) (ht _) (ht _)⟩⟩⟩
end YM.PhysicalNext.Repeat.Legato
