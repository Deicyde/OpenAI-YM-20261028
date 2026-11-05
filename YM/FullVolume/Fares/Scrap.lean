import YM.FullVolume.Fares.Route
/- Acquire tariff & eventual canopy budgets.
 -/
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
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} {T:Campaign R}
set_option quotPrecheck false
local notation "P"=> R.alloy.B.a
local notation "X"=> R.kit
local notation "D"=> R.rolls
local notation "Φ"=> R.alloy.B.a.clock
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I]
open Face Face.Economics
local notation "C"=> R.family
local notation "S"=> R.alloy.B.a.S
open MergeProof.Ribbons Next.Rank Next.Rank.Spindle
namespace Face
-- analytic weights on satellite mesh
open Marker
variable (T:Campaign R) (Θ:Luna.Tableau T.width 300)(v:ℕ→ℕ→ℝ) (hk:Sky R T Θ v)
variable (W:Pillars R T)
variable {n:ℕ} (V₀:Fin n→ R.family.book.Token) (p:ℕ)
include hk
lemma financed (r:ℝ) (hr:0<r) : ∃ b m:ℕ, ∃ (B c:ℝ)(hb:c∈Ray.sun),0 < c ∧ 0≤ B ∧ ∀ j N:ℕ,∀ (h:m ≤ j)(ht:j<N),∀ (a:ℝ)(hp:a∈Ray.sun) (F:Ray.sun→ Face T W), (∀ s:Ray.sun, evalV T W (F s) p N= Muse.Contest.ask (P) (slash a hp s).val) → ∀ o:Fin n→Site ((S).side (j+1) p), spaceout R.family r (j+1,p) o→ PaidBeam (fun s:Ray.sun => ((F (Muse.verso (slash c hb s))).V T W).numeric N p V₀ (((S).toDepth (show j+1≤N from ht) p).embed ∘ o)) (B* (intervalClock R (j+1))^b):=by
     let d(i:Fin n):= (V₀ i).1; let x(i:Fin n): ((Labels.frames G).level (d i)).Coeff:= (V₀ i).2; let B:= Stock.census (Fin n); let k:= Stock.final (Fin n); let t:Fin n→Motion:= fun _=> (1,false)
     obtain ⟨b,hb⟩:= (hk.hired d x).exists -- field order check
     obtain ⟨m,hV⟩:= eventually_atTop.mp (hb.and ((readyFields (R:=R) r hr T.gains.SimpleR).and ((eventually_ge_atTop 1).and (eventually_all.mpr (fun i:Fin n=>eventually_ge_atTop (R.t (d i)))))))
     obtain ⟨c,hc,hC,hφ⟩:= aperture T p m (Fintype.card (Fin n)) 1 -- order
     let Z:= denomination R T p m (Fintype.card (Fin n)); refine ⟨debt b k.val.card,m,max 0 Z,c,hC,hc,le_max_left ..,fun j N h ht a hp F hF o hz=>?_⟩
     let y := garlands R p (j+1) o; have hy: Course m N p B y j:=traveling _ (fun _ h'=> (hV _ h').2.1) (show ∀ i i',i≠i'→_ from hz)
     have he: y N=((S).toDepth ht p).embed ∘ o:= funext fun i=> Ribbons.vect R.family _ _ _ _ ht
     have hu(s: Ray.sun) : scoreItem T W N p F B d x t y k s=((F (Muse.verso s)).V T W).numeric N p V₀ (((S).toDepth (show j+1 ≤ N from ht) p).embed ∘ o):=by
        have hv:= Rising.absolute p N ((F (Muse.verso s)).V T W) d x y k rfl; rw [he] at hv; exact hv
     have h:= polynomial T W N p m hp F hF Θ v (hV m le_rfl|>.2.2.1) B d x t y hk.paid hk.spire hk.sav ht h b (fun _ h=>hV _ h|>.1) (hV m le_rfl|>.2.2.2) hy k c hC hφ -- ordering tighten
     simp_rw [hu] at h; exact h.larger (mul_le_mul_of_nonneg_right (le_max_right ..) (by unfold intervalClock; positivity))
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.financed
