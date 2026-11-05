import YM.RG17.Heading
import YM.OPE.Rough.Factory
import YM.FullVolume.Gables.Vendee

/-!
# Heading/field charges adapter: no switch of Tunes

The second cap certificate uses the SAME `tool` as the one used during actual
field transport on this `Run`. Exports `OPE.FramedColumns` used to estimate
engineering powers (with slack), not series or uniform `K` here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{B:SectionData F}{H:History G} {N p m:ℕ} {Y:Hol G}
variable {S: Desk G (H.S.side (m+1) p)}
variable (P : Tool F H N p m){W:Worth}{u ζ v:ℝ}{D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{T:Heading F}{X:Set Wing}
variable (h:Tool.Cap P B Y W D T u ζ v X) (hw:Well (H.rep N p (m+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))
variable (Q:Gram F Y S ((H.levels.params (m+1)).columns))
set_option quotPrecheck false
local notation "L" => H.S.block m
local notation "s"=> (H.levels.params (m+1)).columns

include h hw
-- Extract the triangular information sitting in the proof of `Tool.stained`.
-- `reads` is independent of the `Cap`'s Heading.
lemma gramColumnsHeading :
    (∀ x, F.coeffSize (T.map x) ≤ W.K (H.levels.clock.J (m+1))*F.coeffSize x ∧
          F.coeffSize (T.map.symm x) ≤ W.K (H.levels.clock.J (m+1))*F.coeffSize x) ∧
    ∀ x, F.coeffSize ((Q.reads P) x - T.leads L x) ≤ barunit L * F.coeffSize (F.core x) := by
   have hs:s≥0:= zero_le_one.trans (H.levels.params (m+1)).columns_ge
   have hf:=h.budget.tiny
   have hz:=h.budget.epsilon
   have hc: 0≤u+ζ*s:= add_nonneg (zero_le_one.trans h.budget.cost) (mul_nonneg hz hs)
   let R := Q.scythe
   have he (i:Tally F):= P.scout h hw R (fun j=> Q.toll (Size.axis F j)) i
   constructor
   · intro x
     have h₀:u ≤ W.K (H.levels.clock.J (m+1)):= le_trans ((le_add_of_nonneg_right (mul_nonneg hz hs)).trans (le_mul_of_one_le_right hc (orbitCost_one_le F))) h.budget.funds
     have h' := mul_le_mul_of_nonneg_right h₀ (Work.G08.size_nonneg F x)
     exact ⟨(h.copies.heading x).1.trans h',(h.copies.heading x).2.trans h'⟩
   · intro x
     let f i:=(P.shot i (Coin.uses (R i))).x
     have hZ: Q.reads P x=repaint F f x:=by
         change (P.pages R x).x = _
         unfold Tool.pages; rw [pencil_x]
         exact Finset.sum_congr rfl (fun i _=> congr_arg (chips F x i • ·) (P.portX h hw R i))
     rw [hZ]
     exact (budgets_orbit F L T f x (ζ*(1+s)) (mul_nonneg hz (add_nonneg zero_le_one hs))
       (fun i=> (he i).2.1)).trans (mul_le_mul_of_nonneg_right hf (Work.G08.size_nonneg F _))
end YM.MergeProof.Matric

namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent
open Muse
open Matric

lemma Campaign.paidColumns {R:Run G} {T:Campaign R} (W:Pillars R T) (h:G.Simple) :
    OPE.FramedColumns R.family R.w := by
   intro d N p hd m hm hn
   let hz:=R.tuning.receipts
   let V := R.stories d N p
   let U := W.yields N p
   have he : ∀ w:R.t d ≤ N, Branch.Piano R.b U (fun i=> Boutique.brochure R.T i p hz) (Nat.zero_le _) (R.accepts d) V w := fun hx=> W.ports d N p hx
   obtain ⟨S,hS⟩:= he hd
   let hi:=R.accepts d |>.trans (R.alloy.B.a.fits.mono hm)
   let D := U.steps m (Nat.zero_le _) hn
   let P := D.castT R.b U.choice hi
   obtain ⟨Y,X,hX,hY⟩:= Boutique.capTriangle h R.b D U.choice hi hz
   -- The OP branch Heading needn't be the one defined by `.chamber.choose`.
   -- But casting the marks, including their forced partners, is unchanged,
   -- so we estimate another property of the actual output coordinates.
   have hx:= U.veering h R.b hz (fun i=> Boutique.brochure R.T i p hz) (Nat.zero_le _) (R.accepts d) m hm hn hS
   let hw := U.notices (fun i=> Boutique.brochure R.T i p hz) (show 0 ≤ m+1 from Nat.zero_le _) hn
   let Q := U.reading R.b (fun i=> Boutique.brochure R.T i p hz) (Nat.zero_le _) (R.accepts d) (m+1) (le_trans hm m.le_succ) hn hS
   have hA := gramColumnsHeading P hX hw Q
   refine ⟨Y,hY,hA.1,fun x=>?_⟩
   change ((Labels.frames G).level d).coeffSize ((V.entries m x).x-_)≤_
   have hp:= hx.2 x
   rw [U.argues h R.b hz (fun i=> Boutique.brochure R.T i p hz) (Nat.zero_le _) (R.accepts d) m hm hn] at hp
   change (V.entries m x).x= Q.reads P (V.entries (m+1) x).x at hp
   rw [hp]
   exact hA.2 _

end YM.PhysicalNext.Repeat.Legato

#print axioms YM.MergeProof.Matric.gramColumnsHeading
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.paidColumns
