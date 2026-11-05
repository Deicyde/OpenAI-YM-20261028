import YM.FullVolume.Dusk.Print
import YM.FullVolume.Dusk.Noa
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp
open Pillars Bandage Pass Muse Contest Ovens
variable {R:Run G} (T:Campaign R)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
local notation "o"=> R.alloy.B.a.clock.bar
open Spirit Branch
open Boutique
open Extraction Extraction.Lease
variable (W: Pillars R T)
-- Diagram frame physical labels.Select.Stream REAL and branch.
structure Face where
    F : ∀ p N, Contest N p T.L
    score : Cantata T F
    owns : Album T W score
namespace Face
def centerF : Face T W := ⟨fun p N=> T.center N p, visible T W,stamped T W⟩
abbrev V (F:Face T W):= F.owns.family T W F.score
abbrev evalV (F:Face T W)(p N:ℕ):ℝ := F.F p N |>.bonusB
variable {T W}
lemma unit p N : evalV T W (centerF T W) p N = R.alloy.B.a.clock.bar:= R.T.choice.reaches ..
-- explicit
lemma gathered (A B:Face T W) (N p:ℕ)(h:Courant (A.score.mat N p) (B.score.mat N p)) {n:ℕ}(v:Fin n→ R.family.book.Token)(hx:R.family.sufficient N v)(y:Fin n→Site (R.alloy.B.a.S.side N p)): (A.V T W).numeric N p v y=(B.V T W).numeric N p v y:=by
    have he : (A.V T W).beta N p=(B.V T W).beta N p:=by
       change (A.score.q N p N).beta =(B.score.q N p N).beta
       rcases N with _|N; rw [A.score.zero,B.score.zero]; rw [h.direct _ (by omega) le_rfl]
    have hv d(h':R.t d ≤ N): (A.owns.record d N p).terminal=(B.owns.record d N p).terminal:=by
       exact devices R.b (A.score.mat N p) (B.score.mat N p) _ _ _ _ _ h' h (A.owns.spent d N p h') (B.owns.spent d N p h') (A.owns.priced d N p h') (B.owns.priced d N p h')
    rw [Family.num,Family.num,he]; congr 1; funext U; refine Finset.prod_congr rfl (fun i _=>?_)
    have hp:=hv _ (hx i); let I:= fun x=> initial (C:=localSection G (v i).1) (R.alloy.B.bake.make A.score.q) N p x (y i) U
    change I _= I _; exact congr_arg I (show (A.owns.record _ N p).terminal.symm (v i).2=(B.owns.record _ N p).terminal.symm (v i).2 from congr_arg (fun f:(((Labels.frames G).level (v i).1).Coeff≃ₗ[ℂ] ((Labels.frames G).level (v i).1).Coeff)=> f.symm ((v i).2: ((Labels.frames G).level (v i).1).Coeff)) hp)
lemma selectedG (A : ℕ→ℕ→ Face T W)(he : ∀ p n:ℕ,|evalV T W (A p n) p n-R.alloy.B.a.clock.bar| ≤ outing T p): ∃ B:Face T W, (∀ p N,B.F p N=(A p N).F p N) ∧ ∀ p N:ℕ, Courant ((A p N).score.mat N p) (B.score.mat N p) :=by
   let Q p N: Contest N p T.L:= (A p N).F p N
   obtain ⟨C,hC⟩:= packs T Q he (fun p n=> (A p n).score) (fun p N=> rfl); exact ⟨⟨Q,C,Classical.choice (hasRecord T W C)⟩,fun p N=>rfl,hC⟩
-- direction packaging.C.
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.gathered
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.selectedG
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.unit
