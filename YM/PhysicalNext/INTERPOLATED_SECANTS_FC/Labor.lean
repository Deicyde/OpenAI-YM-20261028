import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Corridor
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Rate

/-! Can afford the regular cluster tests on actual transitions, EVEN WITHIN a plateau.
First L against inverse/forward costs including any presumed pre-L contribution coefficient
for the sharp singleton & processed unary/binary remainders. No L floor that depends on post-L
sizes; then delay absorbs height and B powers. Not choosing/increasing delay from seeing N,m,p.
Not a proof of the cutoff/cancellation claims of the Deficit and V-jet estimators!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc.Rate
open Lattice Wilson RG Function Filter Set Pressure Push.AbsoluteSums Push.PriceCompiler AnalyticBridge.VerifiedReset
  AnalyticBridge.BranchTuning
open Extra.Multi.Germs (pay)
open scoped Topology BigOperators

variable (G : Gauge) (L : Side) (S : Stage)
def clustersPrice (p : BudgetPoint) (y : ℝ) (N m : ℕ) := Cluster.price p 1 (shrink y hitPower) (shrink y treePower) N m

omit G in
lemma price_pos {p : BudgetPoint} {y : ℝ} (N m : ℕ) (hy : 1 ≤ y) : 0≤ clustersPrice p y N m := by
  have hy' := zero_lt_one.trans_le hy; have := shrink_pos hy' hitPower; have ht := shrink_pos hy' treePower
  have he : 0 ≤ 1-shrink y treePower := sub_nonneg.mpr (shrink_one hy (by unfold treePower; norm_num))
  unfold clustersPrice Cluster.price pay Reserves.polyPrice Reserves.treeYield
  positivity
omit G in
private lemma cluster_bill {p : BudgetPoint} (hS : Time.Same S p) {y : ℝ} (hy : 0<y) (h : shrink y treePower ≤ 1/2) (N m : ℕ) :
    clustersPrice p y N m ≤ (2*Reserves.polyPrice 1 (N+Further.LogJets.orderFee (Time.probe S)) * 4^(S.power*S.order)) *
      (1+(p.B:ℝ))^(S.power*S.order) * shrink y (hitPower+treePower*m) := by
  let k := S.power*S.order; let P := Reserves.polyPrice 1 (N+Further.LogJets.orderFee p)
  have hP : 0≤P := by unfold P Reserves.polyPrice; positivity
  have hp : pay p ≤ 4^k * (1+(p.B:ℝ))^k := by rw [pay,← pow_mul, ← mul_pow, hS.1,hS.2.1]; gcongr; linarith
  have ht := shrink_pos hy treePower
  have hu := shrink_pos hy hitPower
  have hh : (1-shrink y treePower)⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  rw [clustersPrice, Cluster.price,Reserves.treeYield,show Further.LogJets.orderFee (Time.probe S) = Further.LogJets.orderFee p by
    unfold Further.LogJets.orderFee; rw [hS.1,hS.2.1]; rfl,← shrink_mul hy,← shrink_pow hy]
  calc
    _ ≤ (4^k*(1+(p.B:ℝ))^k)*(P*(shrink y hitPower *shrink y treePower^m * 2)) := by
      exact mul_le_mul hp (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (by positivity)) hP) (by
        change 0 ≤ P * (shrink _ _ * shrink _ _ ^m * _); have ht' : 0<1-shrink y treePower := by linarith
        positivity) (by positivity)
    _ = _ := by unfold k P; ring



variable {pre post : ℝ}
omit S in
lemma front_pos (hpre : 0≤pre) (hpost : 0≤post) {y : ℝ} (hy : 0<y) (r : ℝ) : 0 ≤ front pre post L y r := by
  have := shrink_pos hy r; have := shrink_pos hy postPower; unfold front; positivity


def frozenMass (p : BudgetPoint) (pre post : ℝ) (y : ℝ) := front pre post L y size + clustersPrice p y 0 2 + front pre post L y size
def frozenFee (p : BudgetPoint) (pre post : ℝ) (y : ℝ) := 4*(Content.interCoeff * (4*frozenMass L p pre post y) / shrink y lengthPower +
    shrink y lengthPower ^ (Content.depth-1) * (2^Content.depth * 8 * clustersPrice p y Content.depth 0) + 4*frozenMass L p pre post y)






def movingFee (p : BudgetPoint) (pre post : ℝ) (y : ℝ) := Content.interCoeff * frozenMass L p pre post y / shrink y helperPower +
    shrink y helperPower ^ (Content.depth-1) * clustersPrice p y Content.depth 0



end YM.PhysicalNext.InterpolatedSecantsFc.Rate
