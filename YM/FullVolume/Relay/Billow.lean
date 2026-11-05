import YM.FullVolume.Relay.Solo
import YM.FullVolume.Relay.Vault
import YM.FullVolume.Fields.Till
/-
 Roll under unaligned observations with NEW allocations. Keep unit term ν
 throughout. No costs assumed on its size to obtain the pushes; size is
 earned only from initialization at observation. Let posting step below.Stop.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign.Face
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} (T:Campaign R) (W:Pillars R T)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
open Spirit Branch
open Boutique Guard
open Extraction Extraction.Lease
variable (N p m:ℕ)
open UniformSpace
variable {a:ℝ}(haArc:a∈ Ray.sun)
variable (F:Ray.sun→ Face T W)(hF:∀ s:Ray.sun, Face.evalV T W (F s) p N= ask R.alloy.B.a (slash a haArc s).val)
open Veil.Splint Roof.Chord Jams FullVolume.Nectar
local notation "Vt"=>T.gains
local notation "Φ"=> R.alloy.B.a.clock
local notation "Z₁"=>fun s:Ray.sun=> (F (Muse.verso s)).score
local notation "Xo"=>fun s:Ray.sun=> (F (Muse.verso s)).owns
local notation "Wν"=> (R.tuning.receipts)
local notation "P"=>R.alloy.B.a.budget
local notation "R₁"=> arena T W N p F
variable (Θ:Luna.Tableau T.width 300)(v:ℕ→ℕ→ℝ) (H:1 ≤ m)(hN:m<N)
-- s=diameter; λ normalization. independent of cutoff.
include hF H hN
local notation "Ω"=> (Φ).hatBeta m
local notation "n_"=> R.alloy.B.a.S.side m p
-- Shelter cost from gasoline etc.
local notation "Q₀"=> (R.alloy.B.a.budget m)
abbrev fundsPitch (x:ℝ) :ℝ:= 2 /Pass.normedWidth x
abbrev ticker (x:ℝ):= fundsPitch x+ FullVolume.Amp.lux
lemma incomes : ∃ z:Ray.sun→ ℝ, PaidBeam z (ticker ((Φ).hatBeta m)) ∧ (∀ s:Ray.sun,(arena T W N p F m s).beta=Pass.fromLambda ((Φ).hatBeta m) (z s))∧ Feel (fun i:Ray.sun=> (arena T W N p F m i).activities.additive (R.alloy.B.a.budget m)) (Fintype.card (Site (R.alloy.B.a.S.side m p))* ((stageP R.alloy.B.a m p).b)) :=by
    have he:1/2*a∈ Ray.sun:=by obtain ⟨h,hv⟩:=haArc; constructor<;> linarith only [h,hv]
    let V_ (s:Ray.sun):= (F (Muse.verso s)).F p N; let O:= halls T p N
    have hX(i:Ray.sun): (V_ i).bonusB=ask R.alloy.B.a (slash (1/2*a) he i|>.val):=by rw [show (V_ i).bonusB= _ from hF (Muse.verso i)]; apply congr_arg; change _*(1/2)*_= _; change i.val*(1/2)*a=i.val*(1/2*a); ring
    let i:Fin (N+1):= ⟨m,hN.trans N.lt_succ_self⟩
    obtain ⟨B,hB,hq⟩:= Veil.terrace T.gains O V_ he hX i
    let u(s:Ray.sun):= Contest.chair T.gains O (V_ s) i; let z(s):= Contest.pitch (V_ s) i
    have hh'(s): arena T W N p F m s=(V_ s).trail m:= ((F (Muse.verso s)).score).palm N p (H.trans hN.le) m H hN.le
    have hh(s): Urns.observe (salons T p N m hN.le) (u s)=(arena T W N p F m s).activities:= ((V_ s).home_observe T.gains O m hN.le).trans (congr_arg Rep.activities (hh' s).symm)
    have hv: ∀ s:Ray.sun, (arena T W N p F m s).beta= fromLambda ((Φ).hatBeta m) (z s):=fun s=> (congr_arg Rep.beta (hh' s)).trans ((V_ s).spoken T.gains m hN.le).symm
    refine ⟨z,?_,hv,?_⟩
    · obtain ⟨P',Z,hP',hz,hz'⟩:= Veil.jacket T.gains O V_ he hX i; let w:= Ω
      have h:‖z tip‖ ≤ fundsPitch w:=by
         have he:= (V_ Jams.tip).mildS T.gains m hN.le; let u':= Pass.normedWidth w; have hh:0<u':=Pass.widthP (T.gains.largeG.scale m|>.floor); change 17/20 ≤ u' *z tip ∧ u'*z tip ≤23/20 at he
         unfold fundsPitch; rw [le_div_iff₀ hh]; change |z tip| *u' ≤ 2
         rw [mul_comm,← abs_of_nonneg hh.le,← abs_mul, abs_of_nonneg]; · linarith only [he.2]
         linarith only [he.1]
      apply ((PaidBeam.larger (PaidBeam.static (z tip)) h).plus (g:=fun s=> FullVolume.Amp.Beam.read _ s P') (b:= FullVolume.Amp.lux) (by exact ⟨P',hP',fun _=>rfl⟩)).stamp; exact fun s=> (hz' s).1
    simp_rw [← hh]; exact logOrbit (stageP L! i p) (O.plan i (headB i)) hB hq
local notation "W_"=> R.alloy.B.a.params m
local notation "y_"=> R.alloy.B.a.clock.loopCap m
local notation "Q_"=> (P m)
local notation "u'"=> (Φ).hatBeta m
local notation "σ"=> (W_).width
open Push.BetaTransport
-- Actual R.Path constant vs s. true.
lemma immigrant (s t:Ray.sun): (arena T W N p F m s).path=(arena T W N p F m t).path:=by
    have hV(s): arena T W N p F m s=((F (Muse.verso s)).F p N).trail m:= ((F (Muse.verso s)).score).palm N p (H.trans hN.le) m H hN.le
    rw [hV,hV]; let A(v: T.Face W):= (v.F p N).rises.prices m (Nat.zero_le _) hN.le
    exact (A (F (Muse.verso s))|>.1).path.trans (A (F (Muse.verso t))|>.1.path.symm)
local notation "Θ!"=> (W_).paths
local notation "W0"=> (W_).clip
local notation "R0_"=> arena T W N p F m
abbrev tank (G:Gauge)(p:BudgetPoint) (W:RG.Stage) (n:Side) (Λ:ℝ):= (FullVolume.Shroud.Well.gasoline (G:=G) p W.clip W.width W.paths Λ n).choose
abbrev proceedsRate (x:ℝ):= ‖x‖ *((‖Pass.normedWidth x‖* (ticker x))*(‖Pass.normedWidth x‖*(ticker x)))
abbrev logCostVac (R:Run G)(p m:ℕ):ℝ:= proceedsRate (R.alloy.B.a.clock.hatBeta m) * tank G (R.alloy.B.a.budget m) (R.alloy.B.a.params m) (R.alloy.B.a.S.side m p) (R.alloy.B.a.clock.loopCap m) + Fintype.card (Site (R.alloy.B.a.S.side m p)) * PathData.loopsPrice (R.alloy.B.a.budget m) 0 ((R.alloy.B.a.params m).paths) (R.alloy.B.a.clock.loopCap m)+ Fintype.card (Site (R.alloy.B.a.S.side m p))*(stageP R.alloy.B.a m p|>.b)
lemma paid_beta : PaidBeam (fun s=> (arena T W N p F m s).beta) (proceedsRate ((Φ).hatBeta m)) ∧ Feel (fun i:Ray.sun=> (arena T W N p F m i).activities.additive (R.alloy.B.a.budget m)) (Fintype.card (Site n_) * ((stageP R.alloy.B.a m p).b)):=by
    obtain ⟨z,hz,h,ht⟩:=incomes T W N p m haArc F hF H hN; let x(s):=Pass.normedWidth (u')*z s; have hx:= bilimerR (PaidBeam.static (Pass.normedWidth (u'))) hz
    refine ⟨(bilimerR (PaidBeam.static u') (bilimerR hx hx)).stamp ?_,ht⟩; intro i; rw [h,Pass.fromLambda]; change _= _*(_*_); rw [pow_two]
set_option maxHeartbeats 460000 in
lemma normalPay : Feel (baseNo (arena T W N p F m)) (logCostVac R p m):=by
    have he(s) := ((Z₁ s).mat N p).choice.represents N p m hN.le; let x:= arena T W N p F m
    have hP(s): (x s).p=Q_ := (he s).vac; have hW(s): (x s).clip=(W_).clip:= (he s).clip
    let D: PathData G:=(x Jams.tip).path; have hD(s): (x s).path=D:=immigrant T W N p m haArc F hF H hN s tip
    have hk : D.Bounds (W_).clip (W_).width (W_).paths y_:= (hW tip) ▸ (he tip).good.paths
    let u₀:= tank G (R.alloy.B.a.budget m) (R.alloy.B.a.params m) (R.alloy.B.a.S.side m p) (R.alloy.B.a.clock.loopCap m); have h' := (FullVolume.Shroud.Well.gasoline (G:=G) Q_ W0 (W_).width (W_).paths y_ n_).choose_spec
    have hz:0 ≤ y_:=(tsum_nonneg hk.two.1).trans hk.two.2.2
    let C0:= Fintype.card (Site n_)* PathData.loopsPrice (P m) 0 Θ! y_
    have he'(x:Config G n_): ‖D.inChannels (W_).clip -- fix
            Q_ 0 x‖ ≤ C0:= kinetic_tip _ _ hz D hk x
    obtain ⟨hb,hQ⟩:= paid_beta T W N p m haArc F hF H hN
    have hp: Feel (fun (_:Ray.sun) y=> kinetic D (W_).clip Q_ (y:Config G n_)) u₀:= Feel.staticC _ h'.1 (h'.2 D hk)
    have ht: Feel (fun (_:Ray.sun) y=> D.inChannels W0 Q_ 0 (y:Config G n_)) C0:= Feel.staticC _ ((norm_nonneg _).trans (he' 1)) he'
    have hh:= Feel.united (Feel.negR (Feel.united (Feel.timesR (Feel.of_scalar hb) hp) ht)) (Feel.negR hQ)
    let a(s:Ray.sun)(U:Config G n_):= -((x s).beta* kinetic D W0 Q_ U+D.inChannels W0 Q_ 0 U) -(x s).activities.additive Q_ U
    have hEq : baseNo x=a:=by
         funext s y; unfold a baseNo;rw [Rep.exponent,hP,hD,hW, Push.BetaTransport.channels_split y ((x s).beta)]; unfold Rep.scalar; abel
    rw [show arena T W N p F m=x from rfl,hEq]; unfold a; simp_rw [sub_eq_add_neg]; exact hh -- may rewrite Q_.Price includes sub numerical.Could use conv
end YM.PhysicalNext.Repeat.Legato.Campaign.Face
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.normalPay
