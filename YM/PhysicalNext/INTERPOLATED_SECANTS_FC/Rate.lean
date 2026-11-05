import YM.AnalyticBridge.COUPLING_BRANCH_TUNING.Pricing
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Tables
import YM.Extra.ITERATION_NO_LOSS.Post
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.STRESS_FLUX.Haar
import YM.UVNext.PRICED_KERNELS.Order




/-!
# Relative beta prices and some common post-L arithmetic

Use true hatted fine and output beta (not a different coupling from another trajectory);
parameter-difference *units* will be actual incoming beta difference divided by hatted
OUTPUT beta. Constants in continuity/paid derivative regime not allowed to depend on
forest, period or call depth. One spare portion of a beta power for relative movement vs
absolute regular bounds, still at a summable loss sequence on any Levels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc.Rate
open Lattice Wilson RG Filter Function Set Pressure Push.AbsoluteSums Push.PriceCompiler AnalyticBridge.VerifiedReset
  AnalyticBridge.BranchTuning
open scoped Topology BigOperators

def shrink (y q : ℝ) := y ^ (-q)
lemma shrink_pos {y : ℝ} (hy : 0<y) (q : ℝ) : 0 < shrink y q := Real.rpow_pos_of_pos hy _
lemma shrink_mul {y : ℝ} (hy : 0<y) (q r : ℝ) : shrink y q * shrink y r = shrink y (q+r) := by unfold shrink; rw [← Real.rpow_add hy,neg_add]

lemma shrink_pow {y : ℝ} (hy : 0<y) (q : ℝ) (m : ℕ) : shrink y q ^ m = shrink y (q*m) := by unfold shrink; rw [← Real.rpow_mul_natCast hy.le, neg_mul]

lemma shrink_one {y : ℝ} (hy : 1 ≤ y) {a : ℝ} (ha : 0 ≤ a) : shrink y a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)



def velocity : ℝ := 21/20
def size : ℝ := 11/10
def postPower : ℝ := 6/5
def hitPower : ℝ := 5/12
def treePower : ℝ := 2/5
def helperPower : ℝ := 1/20

def lengthPower : ℝ := 1/32

variable (G : Gauge) (L : Side)










-- `pre` must be chosen stagewise BEFORE determining L. `post` can be assigned post-L.
def front (pre post : ℝ) (L : Side) (y r : ℝ) := pre / (L.val:ℝ) * shrink y r + post*shrink y postPower

def screens (S : Stage) (y : ℝ) := Time.credit G S * shrink y size
def fees (S : Stage) (y : ℝ) := Time.credit G S * shrink y velocity
lemma fees_pos (S : Stage) {y : ℝ} (hy : 0<y) : 0 < fees G S y := mul_pos (Time.credit_pos ..) (shrink_pos hy _)



section
variable {G} (z : Levels G)
def actual (z : Levels G) (m : ℕ) := shrink (z.clock.hatBeta m) velocity / z.clock.hatBeta m
def quotes (z : Levels G) : Rates where
  order m := (z.budget m).order
  early := actual z
  outE := actual z
  outK := forceBasis z
  dialE _ := 0
  dialK _ := 0
  keepE m := 2 * actual z m
  keepK m := 2 * forceBasis z m
  loss m := shrink (z.clock.hatBeta m) velocity / 4




end
end YM.PhysicalNext.InterpolatedSecantsFc.Rate
