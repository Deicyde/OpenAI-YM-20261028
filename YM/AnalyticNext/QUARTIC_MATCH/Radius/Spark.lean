import YM.AnalyticNext.QUARTIC_MATCH.Radius.Hills

/-!
# Physical no-hole inverse *inside* a real room

Full gradient and inverse. No-hole (= genuine ALL frequency) price doesn't assert a perturbative
cut/integration gap. Resolvent costs all nonneg shifts. Color code uses ∞ caps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open Purchase Articles Showroom Model
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Warp
section use
open Green (Rows Both address wt)
variable {c : Side} {α β : Type*} [Fintype α] [Fintype β] {i : α→Site c} {j : β→Site c} {M : Matrix α β ℝ} {r s C A : ℝ}
omit [Fintype α] in
lemma narrow (h : Rows i j M r C) (he : s ≤ r) : Rows i j M s C := fun z=> le_trans (Finset.sum_le_sum (fun k _=> mul_le_mul_of_nonneg_right (Wages.wt_le he ..) (abs_nonneg (M z k)))) (h z)
omit [Fintype α] in
lemma weighted (h : Rows i j M r C) (z : Site c) (he : 0 ≤ s) (hr : s≤r) {v : β→ℝ} (hp : 0 ≤ A) (hh : Amount s j z v A) :
    Amount s i z (M*ᵥ v) (C*A) := by
  intro x; rw [Real.norm_eq_abs]
  let w := wt s (i x) z
  have hw : 0 ≤ w := (Green.wt_pos ..).le; have hC := narrow h hr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  change ∑ b : β,|M x b*v b| ≤ _*_
  calc
    _ ≤ ∑ b : β, wt s (i x) (j b)* |M x b| * (A*w) := by
      apply Finset.sum_le_sum; intro b _; rw [abs_mul]
      have he : |v b|≤A*(wt s (j b) (i x)*w) := (hh b).trans (mul_le_mul_of_nonneg_left (Green.wt_triangle he ..) hp)
      rw [Green.wt_symm s (j b) (i x)] at he; apply (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans_eq; ring
    _ ≤ _ := by rw [← Finset.sum_mul]; exact (mul_le_mul_of_nonneg_right (hC _) (mul_nonneg hp hw)).trans_eq (mul_assoc ..).symm
omit [Fintype α] in
lemma baseRows (h : Rows i j M r C) (he : 0≤r) (k) : ∑ b, |M k b| ≤ C := by simpa only [Green.wt,zero_mul,Real.exp_zero,one_mul] using narrow h he k

end use
open Green (Rows Both address wt)
variable {G : Gauge} {c f : Side} (S : StepData c f) (H : Forest S.ratio)

def orderCost (G : Gauge) (s : ℝ) := max 1 ((Fintype.card G.ColorIndex:ℝ)*((Fintype.card Axis:ℝ)*Premium.overall s))
lemma order_ge (G : Gauge) (s : ℝ) : 1 ≤ orderCost G s := le_max_left ..




section costs
variable (Q : Purchase) (G : Gauge) (η : ℝ)
def thick := min (Q.width/2) ((η/2)/curvature Q G)
lemma thicker (he : 0<η) : 0<thick Q G η := lt_min (half_pos Q.pos) (div_pos (half_pos he) (zero_lt_one.trans_le (pays ..)))
lemma shorter : thick Q G η<Q.width := lt_of_le_of_lt (min_le_left ..) (by linarith [Q.pos])

def fraction := Green.factor (η/2) (curvature Q G)
def innerTime := fraction Q G η * Q.vacancy 2
def gets (η : ℝ) := min 1 ((η/2)/2)
lemma willing {η : ℝ} (he : 0<η) : 0<fraction Q G η := lt_min zero_lt_one (div_pos (half_pos (half_pos he)) (zero_lt_one.trans_le (pays ..)))
lemma length_pos {η : ℝ} (he : 0<η) : 0 < innerTime Q G η := mul_pos (willing Q G he) (Q.vacant _)
lemma gets_pos {η : ℝ} (he : 0<η) : 0<gets η := lt_min one_pos (half_pos (half_pos he))

def lease := innerTime Q G η/2
def debits := (gets η)⁻¹*orderCost G (lease Q G η)
lemma lease_pos {η : ℝ} (he : 0<η) : 0<lease Q G η := half_pos (length_pos Q G he)
lemma spends {η : ℝ} (he : 0<η) : 0<debits Q G η := mul_pos (inv_pos.mpr (gets_pos he)) (zero_lt_one.trans_le (order_ge ..))
end costs

variable (p : Clip) (R : PathData G) (θ : S.Choices) {F : Site f→ChartVars H G→ℝ} {Q : Purchase} (hp : Q.Applies H p R F)
    {η : ℝ} (hr : 0<η) (hh : PriceGap H p R η) {x : ChartVars H G} (he : ‖x‖ ≤ thick Q G η)
include hp hr hh he
omit hr in
lemma certifies : Green.Bottom (bend S H p R θ x) (η/2) := by
  have h₀ : ‖(0:ChartVars H G)‖ < Q.width := by simp only [norm_zero]; exact Q.pos
  let B := bend S H p R θ; let T := B x - B 0; let c := Q.vacancy 2; let n := curvature Q G
  have hA : Both (address H) (address H) T c (n*‖x‖) (n*‖x‖) := by
    simpa only [sub_zero] using compare S H p R θ hp (he.trans_lt (shorter ..)) h₀
  have hpp : n*‖x‖≤η/2 := by
    rw [mul_comm]; exact (le_div_iff₀ (zero_lt_one.trans_le (pays ..))).mp (he.trans (min_le_right ..))
  intro v
  have hg := (Green.counted θ hh v)
  have ht := Green.schur T v (η/2) (fun k=> (baseRows hA.1 (Q.vacant _).le k).trans hpp) (fun k=> (baseRows hA.2 (Q.vacant _).le k).trans hpp)
  obtain ⟨hy,h⟩ := abs_le.mp ht
  change _ ≤ dotProduct v (B x *ᵥ v)
  change _ ≤ dotProduct v (B 0 *ᵥ v) at hg
  unfold T at hy; rw [Matrix.sub_mulVec,dotProduct_sub] at hy; linarith



end Warp
end YM.AnalyticNext.QuarticMatch.Radius
