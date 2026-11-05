import YM.FullVolume.Fares.Cash
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
variable {m N n j p:ℕ} {r:ℝ}
abbrev garlands (R:Run G)(p j:ℕ)(o: I→ Site (R.alloy.B.a.S.side j p)) (m:ℕ) (i:I): Site (R.alloy.B.a.S.side m p):= Ribbons.loops R.family j p (o i) m
private lemma shrink (h: m≤ j)(o o': Site (R.alloy.B.a.S.side j p)) : let L:= (R.alloy.B.a.S.toDepth h p); (S).a j*separation o o' ≤ (S).a m*separation (L.parent o) (L.parent o')+(S).a m:=by
    intro L; let i:=L.parent o; let k:= L.parent o'; let Y:= L.embed i; let Z:= L.embed k
    have hh: separation o o'≤ L.count.val* separation i k+ L.count.val:=by
       have hx:= Corona.near L o; have he:= Corona.near L o'; have hz:= separation_triangle o Y o'; have hv:= separation_triangle Y Z o'; rw [separation_comm Z o'] at hv
       have ht: Y=L.embed i:=rfl; rw [ht,show Z=L.embed k from rfl,Station.both] at hv; change 2*separation o Y ≤_ at hx; change 2*separation o' (L.embed k)≤_ at he; change separation Y o'≤ L.count.val*separation i k+_ at hv; omega
    have hp := (S).embeds_scale L
    rw [← hp]; exact le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hh) ((S).a_pos j).le) (le_of_eq (by push_cast; ring))
variable {o:I→ Site (R.alloy.B.a.S.side (j+1) p)}
lemma traveling (B:Marker.Census I)(hv:∀ z:ℕ,m≤ z→(S).a z+(S).a z*((((P).budget z).B:ℝ)^2) ≤ r) (hp:∀ i k,i≠k → r≤ (S).a (j+1)*separation (o i) (o k)): Course m N p B (garlands R p (j+1) o) j:=by
    let f:= garlands R p (j+1) o
    have hD z (h:m≤ z)(i k:I)(hu:i ≠ k): ((P).budget z).B^2 ≤ separation (f z i) (f z k):=by
       let t:= separation (f z i) (f z k); let ζ:= (S).a z; let a:= (S).a (j+1)
       have ht : r ≤ ζ * t + ζ :=by
          rcases le_total (j+1) z with ht | ht
          · let U:= (S).toDepth ht p; have hQ:= Station.both U (o i) (o k); have he (i:I): f z i=U.embed (o i):= Ribbons.vect (C) _ _ _ _ ht
            have hp':ζ*t=a*separation (o i) (o k):=by unfold t; rw [he,he,hQ,Nat.cast_mul,← mul_assoc,show ζ*↑U.count.val=a from (S).embeds_scale U]
            exact le_trans (le_trans (hp _ _ hu) hp'.symm.le) (le_add_of_nonneg_right ((S).a_pos z|>.le))
          let U:= (S).toDepth ht p; have he (i:I): f z i=U.parent (o i):= Ribbons.vote (C) _ _ _ _ ht
          unfold t; rw [he, he]; exact le_trans (hp _ _ hu) (Face.shrink (R:=R) ht _ _)
       have hh := hv z h; let l:= ((P).budget z).B; change ζ+ζ*(l:ℝ)^2≤ r at hh
       rw [add_comm] at ht; have hp':=(le_of_add_le_add_left (hh.trans ht)); have hx:= le_of_mul_le_mul_left hp' ((S).a_pos z); exact_mod_cast hx
    refine ⟨fun z h _=> Extra.Multi.Occupancy.of_injective (Edition.injected _ _ ((P).budget z|>.B_pos) (hD z h)),fun z h _=> ⟨fun _ _ i _ k _=> hD z h i k⟩,?_,?_⟩
    · intro z h hn a
      unfold garlands; rw [Ribbons.vect (C) _ _ _ _ h, Ribbons.vect (C) _ _ _ _ (h.trans z.le_succ)]; exact Station.embed_comp ((S).toDepth h p) _ _ _
    intro z h hx; funext i; unfold garlands Function.comp; dsimp only; erw [Ribbons.vote (C) _ _ _ _ (Nat.succ_le_succ hx), Ribbons.vote (C) _ _ _ _ (hx.trans j.le_succ)]
    exact (Station.parent_nested ((Φ).op z p).ratio ((S).toDepth (Nat.succ_le_succ hx) p) _ ((S).block_odd z) ((S).toDepth_odd (Nat.succ_le_succ hx) p) (o i)).symm
lemma readyFields (r:ℝ) (hr:0<r) (h:G.Simple):∀ᶠ z:ℕ in atTop,(S).a z+(S).a z*((((P).budget z).B:ℝ)^2) ≤ r :=by
    have ht:= (S).shrinks.add (Eves.price (P) h)
    rw [zero_add] at ht; exact ht.eventually (ge_mem_nhds hr)
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.traveling
