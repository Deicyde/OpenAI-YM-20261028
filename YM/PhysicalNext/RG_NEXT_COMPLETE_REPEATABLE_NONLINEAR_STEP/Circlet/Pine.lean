import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Turnstile
import YM.Further.THRESHOLD_SOURCE_RESTART.WellsPrice
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Orchestral
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Upswing
import YM.Planned.PRIMARY_INTEGRAL_295.Decks
import YM.Planned.PRIMARY_INTEGRAL_295.Gala
import YM.Planned.PRIMARY_INTEGRAL_295.Thrift
import YM.ProofPorts.GRID_RENEWED_RESERVES.LedgerSheet
import YM.ProofPorts.GRID_RENEWED_RESERVES.Speeds

/-!
 # Actual axis charge.W prerequisites, with explicit length/depth tests. Align Projection Predictor from PPX (E ppX) WITH calibrated Frame. Primary from Gaussian Christ not identity.V.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Circlet
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
variable {G : Gauge}{d c :ℕ}{n:Side}
section ticket
variable (R:Rep G n)
set_option quotPrecheck false
local notation "T"=> localSection G d
local notation "F"=> (Labels.frames G).level d
local notation "U₁"=> (T).footprint (0:Site n)
lemma ankle : (0:Site n) ∈ (localSection G d).footprint 0:= mem_image.mpr ⟨0,(sound G d).anchored,by simp⟩

variable (i:((Labels.frames G).level d).Index)(hi:i≠0){τ:ℝ}
abbrev hills:= Push.Local.presented T (0:Site n) R.p.threshold (Size.axis F i)
include hi in
lemma canon: Extra.Histories.salary R U₁ (hills R i)= (Extra.Histories.primary 0 (Size.axis F i)).density 0 T R:=by
   funext U; rw [primary_density]; change _ = _*(_+masked R.p.threshold (U₁) ((T).places ((F).scaled _ ((F).core (Size.axis F i))) _) _)
   rw [Size.core_axis,if_neg hi,show Size.axis F i 0=0 from Pi.single_eq_of_ne hi.symm _,zero_add]; rfl
-- mark.Cloud certificate ht includes Reveal sections.
variable (h : Push.Local.Readable (hol G) (localSection G d) R.p n τ)(hs: HasSlots R.p R.activities)
include h in
lemma lofty: R.p.Regular U₁ (hills R i)∧R.p.supBounds 0 U₁ (hills R i) τ:=by
   have ht:=Push.Local.presented_good 0 h (Size.axis _ i);
   rw [Size.size_axis,mul_one] at ht; exact ht
-- Note: h unindexed J horizon yet.

abbrev badge (G:Gauge)(n:Side)(d:ℕ):=Blush.found (0:Site n) ((localSection G d).footprint _) (ankle)
def lark := Blush.float R 0 U₁ ankle _ _ (lofty R i h).1 (lofty R i h).2 hs

local notation "B" => badge G n d
include hs in
lemma signboard : R.activities.reg (badge G n d)=reg 0 U₁ ankle:= Blush.latch _ _ _ _ hs


lemma skin : (lark R i h hs).live.crest=U₁:=by change (R.activities.reg (badge G n d)).support=_; rw [signboard R hs]
include hi h
lemma shines (j:ℂ→L[ℝ] ℝ)(hp:2≤ n.val): Peak.lit 0 U₁ (j ∘ hills R i) (((F).grades i).1-1):=by
   have hL := nonwrapping_placement T 0 h.fit; have hm: ((F).grades i).1-1≤d:= (Nat.sub_le ..).trans ((F).bound i)
   apply Peak.spoke _ _ _ _ (lofty R i h).1 hL hp (hm.trans h.order) hm
   exact GridRenewal.Speed.canon_first _ hi h
lemma larkS : (lark R i h hs).milk=(Extra.Histories.primary 0 (Size.axis F i)).density 0 T R:= ((Blush.balm R 0 U₁ ankle _ _ (lofty R i h).1 (lofty R i h).2 hs).symm).trans (canon R i ‹_›)
-- repay inputs
omit hi
lemma tallyH (hs':minSide G d ≤ R.p.B):
     R.p.mass (lark R i h hs).live.crest (lark R i h hs).live.weight ≤ Real.exp R.p.supportExponent * τ:=by
   have hv := close_stencil G d R.p.B _ hs' (0:Site n); have ht:= h.nonneg; unfold BudgetPoint.mass
   rw [skin]; apply mul_le_mul_of_nonneg_right _ ht
   have he: (coverNumber R.p.B U₁:ℝ) ≤ 1 := by exact_mod_cast hv
   exact Real.exp_monotone (mul_le_of_le_one_right R.p.exponent_pos.le he)
-- exact.Copies
lemma inks (A : ℂ→L[ℝ]ℝ)(h₁:∀ t, ‖A t‖ ≤ ‖t‖):
    let S := cove R 0 U₁ ankle _ _ (lofty R i h).1 (lofty R i h).2 A h₁ hs
    S.turn=.logKey B ∧ S.weight=τ∧ S.ingredient=masked R.p.threshold (R.activities.reg B).support (A ∘ hills R i) ∧ R.p.Regular (R.activities.reg B).support (A ∘ hills R i) ∧ R.p.supBounds 0 U₁ (A ∘ hills R i) τ:=by
   intro S; rw [signboard R hs]; refine ⟨rfl,rfl,?_,Graces.readings A (lofty R i h).1, Graces.pricesL A (lofty R i h).1 h₁ _ (lofty R i h).2⟩
   funext V; change A (masked R.p.threshold (U₁) _ V)= masked R.p.threshold (U₁) _ V; by_cases ht:Healthy R.p.threshold (U₁) V; simp only [masked_eq _ _ _ _ ht,comp_apply];rw [masked_ne _ _ _ _ ht,masked_ne _ _ _ _ ht,map_zero]
end ticket
end YM.PhysicalNext.Repeat.Circlet
