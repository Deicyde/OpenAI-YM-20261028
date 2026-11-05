import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.ClusterJets
import YM.MergeProof.Apres
import YM.MergeProof.Eureka
import YM.MergeProof.Gist
import YM.MergeProof.Ravine
import YM.Next.RANK.Rifle
import YM.Next.RANK.Screen
import YM.Planned.PRIMARY_INTEGRAL_295.Landings

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}
open YM.MergeProof Bandage Accent
section
variable (Q:ℕ→ℕ) {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A) (t:ℕ→ℕ)
set_option quotPrecheck false
local notation "T!"=>Issue.trail Y
local notation "L!"=> (Labels.frames G)
local notation "C!" => (fun (Xf:∀ d N p:ℕ,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p)=> Family.mk (Issue.trail Y) (hol G) (Labels.frames G) (localSection G) t Xf)
local notation "a'"=> A.B.a
include b
variable (h : Steam Q A.delay)(hQ:Monotone Q)(hQ':∀ i:ℕ,1 ≤ Q i)(hp:Mallow.Minty X.shape Q A.delay)(hE:∀ m:ℕ,100  ≤  (A.B.a.budget m).supportExponent) (hG:G.Simple)(hx:∀ d,d+3 ≤ A.B.a.clock.J (t d))(H':Nest X Y) {D:∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail Y).rep N p (m+1)) ((Issue.trail Y).rep N p m)}
     (he:∀ N m p (hm:m<N), Climbs X Y N m p (D N p m hm)) {Xf:∀ d N p:ℕ,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p}(hf:∀ d N p,t d ≤ N→Freight Y H' N p d (Xf d N p) (t d) K (D N p))
include h hQ hQ' hp hE hG hx H' he hf
lemma chaletrail (cost:ℕ→ℕ→ℝ)(d':ℕ→ℕ) (T:∀ d:ℕ,SectionData ((Labels.frames G).level d))(R:Push.Mark.Weave G)(hM:∀ d,Push.Mark.Portfolio (hol G) (T d) (R d))(hc:dusk A.delay cost)(hN:paper M.p cost T d') (hF: d' ≤ M.p.floorL)(H:(C! Xf).Makes) : Scrim (C! Xf) K (far a') (waybill a') (near a') (renal a') (fly a') (mutt a' Q) D ∧ ∃ P b, Scotia (C! Xf) R P b:=by
    let F:= C! Xf; let S:= A.B.a; let E:=F.labels; let J:=S.clock.J; let z:= F.path
    have hW(i:ℕ)(d:ℕ)(he:t d ≤ i):d+3  ≤  J i:= (hx d).trans (A.B.a.fits.mono he)
    have hu (i:ℕ)(d:ℕ)(he:d  ≤  J (i+1)):= hN d (J (i+1)) he _ ((hF _).trans (P.large (J (i+1))).need)
    have hw(i):= hc _ _ (step_paid _ i) _ (A.B.valid.pays i)
    have hS:Scrim F K (far a') (waybill a') (near a') (renal a') (fly a') (mutt a' Q) D:=by
      refine ⟨nectar Q b Y t h hQ hp hE hG hx H' he hf,fun i=> hQ' _,fun d i _=> inv_pos.mpr (pow_pos (zero_lt_one.trans (S.fits.delayed i)) _),fun d i hh=>?_, fun d N p i h_ hI=>?_⟩
      · have hd: d  ≤  J i:= (Nat.le_add_right d 3).trans (hW i d hh); change MergeProof.sap (S.clock.hatBeta (i+1))*((S.S.block i).val:ℝ)^(d+1)*fog _ d (S.clock.hatBeta i)  ≤  fog _ d (S.clock.hatBeta (i+1)); unfold S; rw [Extra.Iteration.block_beta (a:=a'), Extra.Iteration.block_eq A.B.valid]; exact ((hw i).2 d hd).2
      refine ⟨_,ravine hG b Y H' N p i hI d (hW i d h_) (he N i p hI) ?_⟩; rw [params_eq A.B.valid,Extra.Iteration.block_eq A.B.valid]; exact (hu i 0 (Nat.zero_le _)).2.2.2 _ (S.fits.mono i.le_succ)
    have hg:Fridge F (far a') (fly a'):= freezes hG (fun N p=>⟨Guard.Keeper.sufficient (H'.born N p)⟩) (fun i=> ?_)
    · refine ⟨hS,reception H (Stock.consumes A.B.valid A.prices) hS hg T R hM hG ?_⟩
      intro d; let b:= fun i=> cost d (J i)
      have h₀ : ∀ᶠ i:ℕ in atTop, ∃ j,i=j+1∧ d ≤ J (j+1) := by
         filter_upwards [eventually_gt_atTop (t d)] with i hi; obtain ⟨j,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0); exact ⟨j,rfl,(Nat.le_add_right d 3).trans (hW (j+1) d hi.le)⟩
      refine ⟨b,⟨?_, ?_,?_⟩⟩
      · filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi; change Bid.Credit _ (a'|>.params (j+1)|>.order) (a'|>.params (j+1)|>.power) _; rw [params_eq A.B.valid]; exact (hu j d h).2.1
      · filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi; exact ⟨(hu j d h).2.2.1,(hw (j+1)).2 d h|>.1⟩
      filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi
      change 2*(1+(a'|>.params _|>.columns))*sphere (a'|>.params _) ((T _).stencil∪(localSection G _).stencil).card (b _)  ≤  Bid.puffs (A.B.a.S.block _)*sliver (Labels.frames G|>.level d)
      rw [params_eq A.B.valid,show j+1-1=j from rfl,Extra.Iteration.block_eq A.B.valid]; exact (hu j d h).1
    change step_cost (A.B.a.params i) ≤  S.clock.hatBeta i; rw [params_eq A.B.valid]; exact (hw i).1
end
end YM.PhysicalNext.Repeat.Legato
