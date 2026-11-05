import YM.MergeProof.Almandine
import YM.MergeProof.North.Freckles
import YM.MergeProof.North.Siroco
import YM.MergeProof.North.Tibetan
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Seats


/-! Calendared proof thru actual Base+Seed. Can pay more beforeL, delays and Wait. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
open YM.MergeProof.Ribbons
open Mallow
variable (hG:G.Simple) {M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{K:ℕ→ℝ}{W:Bid.Worth}(b:Bandage X K W)(Y:Bolt A)(Q:ℕ→ℕ)
variable (t:ℕ→ℕ)(Z:∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p)(D:∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail Y).rep N p (m+1)) ((Issue.trail Y).rep N p m))
set_option quotPrecheck false
local notation "C"=> Family.mk (Issue.trail Y) (hol G) (Labels.frames G) (localSection G) t Z
local notation "a"=>A.B.a
local notation "U"=>A.B.a.budget
local notation "J"=> A.B.a.clock.J
local notation "x"=> A.B.a.clock.hatBeta
def bling (T:Levels G)(m:ℕ):= Real.exp (Real.sqrt (T.clock.hatBeta (m+1)))
structure Velour (S:Family G)(δ:ℕ→ℝ)(r:ℕ→ℕ) (D:∀ N p m:ℕ,m<N→GaugeDoor (S.path.rep N p (m+1)) (S.path.rep N p m)) : Prop where
   mother : ∃ χ:ℕ→ℝ,∀ d:ℕ,Wares S (μ:=D) (δ:=δ) (r:=r) (S.ref d) d χ δ (bling S.path.levels)
   costs i : let c:=S.path.levels; ((c.budget i).supportExponent+1/2)*peepers c i ≤ Real.sqrt (c.clock.hatBeta (i+1))
variable (hN:Chateau b Q Y t Z D)(ht:∀ m:ℕ,100 ≤ (A.B.a.budget m).supportExponent)
include hN hG ht
lemma exodus (hv:Mallow.AccordV X.shape Q A.delay) (hV :∀ i j,StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) : Velour C (renal A.B.a) (mutt A.B.a Q) D:=by
   let y m:= straw (X.shape.μ (J (m+1)) (J m)) (P.L (J (m+1))) G (x m)
   let o m:= station (x (m+1)); have h(i): x (i+1)=Pressure.betaF G (x i) (P.L (J (i+1))):= by rw [Extra.Iteration.block_beta,Extra.Iteration.block_eq A.B.valid]
   have hA(d i:ℕ)(hi:t d ≤ i): d+3≤ J i:= (hN.opens d).trans (A.B.a.fits.mono hi)
   have hm(i j:ℕ)(hi:j ≤ J i) := hv _ _ (A.B.valid.pays i) _ (step_paid _ _) j hi
   have hf(N p m:ℕ)(hp:m<N):= paneer hG b Y hp Q hN.nest (hN.motion N m p hp) hN.wall.hold (hN.wall.word _ _ (A.B.valid.pays m) _ (step_paid _ _)) (ht _) (ht m)
   refine ⟨⟨y,fun d=> ⟨⟨o,⟨fun N p i he h=>⟨(hf N p i h).1,sewed hG b Y h Q hN.nest (hN.motion N i p h) hN.wall.hold (hN.wall.word _ _ (A.B.valid.pays i) _ (step_paid _ _)) (ht _) (ht _)⟩,fun i _=>(hf (i+1) 0 i i.lt_succ_self).2⟩⟩,fun i _=> (hm i 0 (Nat.zero_le _)).2.2.1,fun i _=> (hf (i+1) 0 i i.lt_succ_self).2.hats,fun i _=>?_,fun i _=>Real.one_le_exp (Real.sqrt_nonneg _),fun i ho N p he=>?_⟩⟩,fun i=>?_⟩
   · let I:= M.p.profile (J i); have hz: (U i).supportExponent= I.supportExponent:=congr_arg Stage.supportExponent (params_eq A.B.valid _)
     change (((U i).B+(U i).B+1:ℕ):ℝ)^4*scurry A.B.a (mutt A.B.a Q) y (renal A.B.a i) i ≤1/2 ∧ Real.exp (scurry A.B.a (mutt A.B.a Q) y (renal A.B.a i) i)-1 ≤1; unfold scurry renal; rw [hz,h i]; exact ⟨(hm i 0 (Nat.zero_le _)).1,(hm i 0 (Nat.zero_le _)).2.1⟩
   · let D:= J i; have hx:=hA d i ho; change MergeProof.Float.Runs _ (A.B.a.clock.op i p) (6*((A.B.a.S.block i).val:ℝ))∧ MergeProof.Throws _ _ _ i _ _ _ (bling A.B.a i)
     rw [Extra.Iteration.block_eq A.B.valid]; apply thaw hG b Y he hN.nest (hN.motion _ _ _ he) d hx (hV _ _ (step_paid _ _)); unfold bling; rw [h i]; exact (hm i d (le_trans (Nat.le_add_right ..) hx)).2.2.2.2
   change ((U i).supportExponent+1/2)*peepers A.B.a i≤Real.sqrt (x (i+1)); rw [h i,show (U i).supportExponent= _ from congr_arg Stage.supportExponent (params_eq A.B.valid i)] -- need adjust? let intro
   exact (hm i 0 (Nat.zero_le _)).2.2.2.1
end YM.PhysicalNext.Repeat.Legato
