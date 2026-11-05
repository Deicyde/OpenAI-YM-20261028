import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Circlet.Pine
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Circlet.Range
/-!
# Budgeting the off-center cell. Specializes to Y parent 0, not shifted masks.

Follows `Circlet.ankle` through `Circlet.setting` with the nonwrapping
check at the corresponding parent, estimate paid using the centered cell
preimage also for enlargement. No switch of Tube.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.RG05Cell
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury Graces
open Planned.PrimaryIntegral295
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {d:ℕ}
section tag
variable {n :Side}(R:Rep G n) (x:Site n)
set_option quotPrecheck false
local notation "T"=>localSection G d
local notation "F"=>(Labels.frames G).level d
local notation "Xp" => (T).footprint x
lemma toe (x:Site n) : x∈(localSection G d).footprint x:=mem_image.mpr ⟨0,(sound G d).anchored,by simp⟩
variable (i:((Labels.frames G).level d).Index)(hi:i≠0){τ:ℝ}
abbrev hills := Push.Local.presented (T) x R.p.threshold (Size.axis (F) i)
variable (h : Push.Local.Readable (hol G) (localSection G d) R.p n τ)(hs: HasSlots R.p R.activities)
include h in
lemma costs: R.p.Regular Xp (hills R x i) ∧ R.p.supBounds x Xp (hills R x i) τ:=by
   have ht:=Push.Local.presented_good x h (Size.axis _ i)
   rw [Size.size_axis,mul_one] at ht; exact ht
abbrev tab (G:Gauge)(x:Site n)(d:ℕ):=Blush.found x ((localSection G d).footprint x) (toe x)
def wood := Blush.float R x Xp (toe _) _ _ (costs R x i h).1 (costs R x i h).2 hs
local notation "B" => tab G x d
include hs in
lemma signed : R.activities.reg (tab G x d)=Blush.reg x Xp (toe x):= Blush.latch _ _ _ _ hs
lemma place : (wood R x i h hs).live.crest=Xp:=by change (R.activities.reg (B)).support=_; rw [signed R x hs]
include h hi in
lemma shine (j:ℂ→L[ℝ]ℝ)(hp:2≤n.val): Peak.lit x Xp (j∘ hills R x i) ((F|>.grades i).1-1):=by
   have hL:= nonwrapping_placement (T) x h.fit
   have hm: ((F).grades i).1-1≤d:= (Nat.sub_le ..).trans ((F).bound i)
   apply Peak.spoke _ _ _ _ (costs R x i h).1 hL hp (hm.trans h.order) hm
   exact GridRenewal.Speed.canon_first _ hi h
lemma tally (hs':minSide G d ≤ R.p.B): R.p.mass (wood R x i h hs).live.crest (wood R x i h hs).live.weight ≤ Real.exp R.p.supportExponent * τ:=by
   have hv:= close_stencil G d R.p.B n hs' x
   unfold BudgetPoint.mass; rw [place]; refine mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_of_le_one_right R.p.exponent_pos.le ?_)) h.nonneg
   exact_mod_cast hv
lemma stone (A:ℂ→L[ℝ]ℝ)(ha:∀ t,‖A t‖≤‖t‖):
    let S:= cove R x Xp (toe x) _ _ (costs R x i h).1 (costs R x i h).2 A ha hs
    S.turn=.logKey B ∧ S.weight=τ∧ S.ingredient=masked R.p.threshold (R.activities.reg B).support (A ∘ hills R x i) ∧ R.p.Regular (R.activities.reg B).support (A ∘ hills R x i) ∧ R.p.supBounds x Xp (A ∘ hills R x i) τ:=by
   intro S; rw [signed R x hs]; refine ⟨rfl,rfl,?_,Graces.readings A (costs R x i h).1,Graces.pricesL A (costs R x i h).1 ha τ (costs R x i h).2⟩
   funext U; change A (masked R.p.threshold (Xp) (hills R x i) U)=masked R.p.threshold Xp _ U
   by_cases ht: Healthy R.p.threshold Xp U; rw [masked_eq _ _ _ _ ht,masked_eq _ _ _ _ ht]; rfl
   rw [masked_ne _ _ _ _ ht,masked_ne _ _ _ _ ht,map_zero]
end tag
variable {c f:Side}{S:StepData c f}{x:ℝ}{r:ℕ}{P B:BudgetPoint}{Y:Support c} (o:Site f)
lemma size (hw: Walled S ((localSection G d).footprint o) Y x r) (ht:P.B=radiusB x) (hs:B.B≤2*P.B)
    (ha:minSide G d ≤ B.B) (hq:11*Planned.AtomRegular.toll r ≤ P.B) (hp:100*(r+20)*(P.B+1)≤ c.val):
    Nonwrapping Y (S.ratio.parent o) ∧ coverNumber P.B Y ≤ P.B:=by
   have he:=close_stencil G d B.B f ha o
   let U:= (localSection G d).footprint o
   have h0:=P.B_pos
   have hm:Y ⊆ Footprint.enlargement S.ratio r P.B U:=ht.symm ▸ hw
   constructor
   · intro y hy
     have hh:= Footprint.where_from S.ratio r P.B B.B U (toe o) (hm hy) h0 hs
     unfold Footprint.extentCost at hh
     have he:1+coverNumber B.B U ≤ 1+1:= Nat.add_le_add_left he _
     have hk:10*((r+20)*P.B*(1+1))< c.val:=by nlinarith only [hp,h0,Nat.zero_le r]
     exact lt_of_le_of_lt (Nat.mul_le_mul_left 10 (hh.trans (Nat.mul_le_mul_left _ he))) hk
   have hv:= Corona.collapse S.ratio U B.B P.B h0 hs r
   apply (Corona.cover_mono hm _).trans; apply Nat.le_of_mul_le_mul_left _ S.patch.L.property
   apply hv.trans
   let L:=S.patch.L.val; have hL:= S.patch.L.property
   have hx:L+10*coverNumber B.B U ≤ L*11:= by change coverNumber B.B U ≤ 1 at he; have hL:1≤L:=hL; omega
   apply (Nat.mul_le_mul_right (Planned.AtomRegular.toll r) hx).trans; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hq
end YM.PhysicalNext.Repeat.RG05Cell
