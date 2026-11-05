import YM.MergeProof.North.Tibetan
import YM.OPE.Replicas.Pass

/-!
# Sharpen conversion pays, even for `Throws` from only a Blade
Achieve a uniform post-L coupling power (log history-scale cost), rather than
exp(sqrt(s)); needs further delay after-L. Equation with `AccordV`
not used as if that already were this improvement. Doesn't spend on altering
any period or mask for the proof. Adapted from MergeProof/North/Tibetan.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
open MergeProof.Ribbons Graces
variable (G : Gauge) (Z : Stage) (L : Side) (d : ℕ)
private def bucks (x : ℝ) (a : ℝ) := 2*(L.val:ℝ)^d*(Mercury.volt x Z.order Z.power*a)
-- simplify unused G warning

def Upgrade (x : ℝ) : Prop := 1 ≤ betaF G x L ∧
  (coinFee G Z d L+|bucks Z L d x (betaF G x L ^ (1/2:ℝ))|)*Graces.host G Z d ≤ betaF G x L

theorem enhanced : ∀ᶠ x in atTop, Upgrade G Z L d x := by
   let f x:= bucks Z L d x (betaF G x L ^ (1/2:ℝ))
   have hf: Rate G L (1/2) (fun x=>|f x|):= by
       have hz: Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
       have hp: Rate G L (1/2) (fun x=> betaF G x L ^ (1/2:ℝ)):= Rate.power
       have hh: Rate G L (1/2) f:= ((((hz.pow (Z.power*Z.order)).weaken (b:=0) (by simp)).mul_right _|>.mul hp).mul_left _|>.weaken (by linarith))
       exact hh.compare (v:=fun x=>|f x|) (by filter_upwards with x; rw [abs_abs])
   have hh:= (((Rate.const (coinFee G Z d L)).weaken (by norm_num : (0:ℝ)≤1/2)|>.add hf).mul_right (host G Z d))
   filter_upwards [(Work.E09.betaF_growth G L).eventually_ge_atTop 1,hh (1:ℝ) (by norm_num)] with x hx ht
   exact ⟨hx,(le_abs_self _).trans (ht.trans_eq (Real.rpow_one _))⟩

theorem Upgrade.pays {x : ℝ} (h : Upgrade G Z L d x) {P : Teller G} (Q : ConnectedActivityE6.Target G P) :
    (coinFee G Z d L+|2*((L).val:ℝ)^d*(Mercury.volt x Z.order Z.power*(Q.goal L x)⁻¹)|)* Graces.host G Z d ≤ betaF G x L:= by
  unfold Upgrade at h
  let e:= betaF G x L
  let A:= Mercury.volt x Z.order Z.power
  have ht: (0:ℝ)≤ Graces.host G Z d := (Graces.simpleH G Z d).le
  refine le_trans ((mul_le_mul_of_nonneg_right (add_le_add_right ?_ _) ht) : _ ≤ _) h.2
  unfold bucks
  repeat rw [abs_mul]
  have he: 0<e:= zero_lt_one.trans_le h.1
  rw [Target.goal,← Real.rpow_neg he.le, abs_of_pos (Real.rpow_pos_of_pos he _),abs_of_pos (Real.rpow_pos_of_pos he _)]
  have hlt : -Q.rate ≤ 1/2:= by linarith only [Q.start]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h.1 hlt) (abs_nonneg _)
end YM.PhysicalNext.Repeat.Mallow
