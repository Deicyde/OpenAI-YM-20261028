import YM.UVExtension.Orchard.Muesli
import YM.MergeProof.Inns
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Harvest
open Finset Set Function Filter MeasureTheory Lattice RG Wilson Precision Labels
open Extra.Histories Source Cells Extraction Next.Extract Dash MergeProof
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge} {C:Family G}
-- all true admitted materials.Additive.Canon.Spirit.Frame
structure Harrow (C:Family G) (α:ℕ→ℝ) (ζ:ℕ→ℕ→ℝ) : Prop where
   lab : Fridge C α ζ
   wage (d) : ∃ (V:SectionData (C.labels.level d))(R:Push.Mark.Weave G)(E:ℕ→ℝ), Push.Mark.Portfolio C.params V (R d)∧ Braze (C:=C) V E
end YM.UVExtension.Harvest
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}
open YM.MergeProof Bandage Accent
open UVExtension.Harvest
section
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}
variable (hG:G.Simple)(t:ℕ→ℕ)(hx:∀ d,d+3 ≤ A.B.a.clock.J (t d))
     {B : Vintage.YM.Org.Bolt A} {S : Factor A} (h:Vintage.YM.PhysicalNext.Repeat.Graces.Nest S B)
     (X:∀ d N p:ℕ,TransferData ((Labels.frames G).level d) (Vintage.YM.Extra.Histories.Issue.trail B) N p)(H:Vintage.YM.Family.Makes (Family.mk (Vintage.YM.Extra.Histories.Issue.trail B) (hol G) (Labels.frames G) (localSection G) t X))
local notation "V'"=> Family.mk (Vintage.YM.Extra.Histories.Issue.trail B) (hol G) (Labels.frames G) (localSection G) t X
local notation "T!"=> A.B.a
-- really shared E attendance across all regulators. use packing V(N,p) not comparing to center's bins
include hx hG h
lemma insured (cost:ℕ→ℕ→ℝ)(d':ℕ→ℕ) (T:∀ d:ℕ,SectionData ((Labels.frames G).level d))(R:Push.Mark.Weave G)(hM:∀ d,Push.Mark.Portfolio (hol G) (T d) (R d))(hc:dusk A.delay cost)(hN:paper M.p cost T d') (hF: d' ≤ M.p.floorL) : Harrow (Family.mk (Vintage.YM.Extra.Histories.Issue.trail B) (hol G) (Labels.frames G) (localSection G) t X) (far A.B.a) (fly A.B.a):=by
    let F:= V'; let U:= A.B.a; let E:=F.labels; let J:=U.clock.J; let z:= F.path
    have hW(i:ℕ)(d:ℕ)(he:t d ≤ i):d+3  ≤  J i:= (hx d).trans (A.B.a.fits.mono he)
    have hu (i:ℕ)(d:ℕ)(he:d  ≤  J (i+1)):= hN d (J (i+1)) he _ ((hF _).trans (P.large (J (i+1))).need)
    have hw(i):= hc _ _ (step_paid _ i) _ (A.B.valid.pays i)
    have hg:Fridge F (far A.B.a) (fly A.B.a):= freezes hG (fun N p=>⟨Guard.Keeper.sufficient (Vintage.YM.PhysicalNext.Repeat.Graces.Nest.born h N p)⟩) (fun i=> ?_)
    · refine ⟨hg,fun d=>?_⟩; let b:= fun i=> cost d (J i)
      have h₀ : ∀ᶠ i:ℕ in atTop, ∃ j,i=j+1∧ d ≤ J (j+1) := by
         filter_upwards [eventually_gt_atTop (t d)] with i hi; obtain ⟨j,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0); exact ⟨j,rfl,(Nat.le_add_right d 3).trans (hW (j+1) d hi.le)⟩
      refine ⟨T d,R,b,hM d, ⟨?_, ?_,?_⟩⟩
      · filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi; change Bid.Credit _ (T!|>.params (j+1)|>.order) (T!|>.params (j+1)|>.power) _; rw [params_eq A.B.valid]; exact (hu j d h).2.1
      · filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi; exact ⟨(hu j d h).2.2.1,(hw (j+1)).2 d h|>.1⟩
      filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi
      change 2*(1+(T!|>.params _|>.columns))*sphere (T!|>.params _) ((T _).stencil∪(localSection G _).stencil).card (b _)  ≤  Bid.puffs (A.B.a.S.block _)*sliver (Labels.frames G|>.level d)
      rw [params_eq A.B.valid,show j+1-1=j from rfl,Extra.Iteration.block_eq A.B.valid]; exact (hu j d h).1
    change step_cost (A.B.a.params i) ≤  U.clock.hatBeta i; rw [params_eq A.B.valid]; exact (hw i).1
end
end YM.PhysicalNext.Repeat.Legato
