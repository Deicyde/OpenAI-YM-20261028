import YM.Push.STATIONARY_UNIFORM.Calculus
import YM.Work.F02.Path


/-!
# Jets of genuine (noncommuting) travel

No upper bound by `‖1:G.Mat‖^length`, which would consume our path widths.
Dimension in the inputs may include the full volume; use a reciprocal-length
Cauchy radius on letters and F02's ambient product which sees the physical
unitaries even for arbitrary basepoints.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Pressure
open Work.F02
open Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {n : Side} {N : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {f g : E → G.El} {C D : ℝ}

lemma Allows.inverse (h : Allows N (fun y => G.mat (f y)) x C) : Allows N (fun y => G.mat (f y)⁻¹) x C := by
  let L : G.Mat ≃L[ℝ] G.Mat := starL ℝ
  have he (y) : G.mat (f y)⁻¹ = L (G.mat (f y)) := G.mat_inv (f y)
  simp_rw [he]
  rw [← one_mul C]
  apply Allows.linear L.toContinuousLinearMap h
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u; change ‖star u‖ ≤ _; rw [norm_star,one_mul]

lemma Allows.times (h : Allows N (fun y => G.mat (f y)) x C) (h' : Allows N (fun y => G.mat (g y)) x D) :
    Allows N (fun y => G.mat (f y*g y)) x (2^N*C*D) := by
  simp_rw [G.mat_mul]
  simpa only [mul_one,ContinuousLinearMap.mul_apply'] using h.bilinear _ h' (ContinuousLinearMap.opNorm_mul_le ℝ G.Mat)

def traceCharge (G : Gauge) : G.Mat →L[ℝ] ℝ :=
  (-(G.repDim : ℝ)⁻¹) • Complex.reCLM.comp (Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap

-- Expose norm with fixed spaces

def priceCost (G : Gauge) (C : ℝ) :=
  let normL {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) := ‖L‖
  1 + normL (E:=G.Mat) (F:=ℝ) (traceCharge G)*C

lemma Allows.price (h : Allows N (fun y => G.mat (f y)) x C) : Allows N (fun y => G.price (f y)) x (priceCost G C) := by
  have he (u : G.El) : G.price u = 1 + traceCharge G (G.mat u) := by
    unfold Gauge.price traceCharge
    change _ = 1 + (-(G.repDim:ℝ)⁻¹)*(G.mat u).trace.re
    ring
  simp_rw [he]
  exact (allows_const (n := N) x (v:=(1:ℝ)) (C:=1) (by simp)).add (h.linear (traceCharge G) le_rfl)

/-- Cost of any walk up to this length. `C` bounds real per-link G.mat
jets. Input norms arbitrary, not implicitly using sup-to-l2 here. -/
def travelCost (G : Gauge) (N a : ℕ) (C : ℝ) := composeCost N
    ((Real.exp 1 * ‖(1:G.Mat)‖) * ((1+ (2:ℝ)^N*(1+a))^N)) C

lemma allows_ambient {U : E → Config G n} (h : ∀ i, Allows N (fun y => G.mat (U y i)) x C) :
    Allows N (fun y => physical (U y)) x C := by
  have hc := (h (Classical.arbitrary _)).nonneg
  exact allows_pi hc fun i => (h i).pair ((h i).inverse (f:=fun y => U y i))

lemma travel_jets {U : E → Config G n} (h : ∀ i, Allows N (fun y => G.mat (U y i)) x C) {w : Walk} (s : Site n)
    {a : ℕ} (ha : w.length ≤ a) : Allows N (fun y => G.mat (travel (U y) s w)) x (travelCost G N a C) := by
  let f (M : Ambient G n) := stringMat M w s
  let r := (1+(a:ℝ))⁻¹; let m := Real.exp 1 * ‖(1:G.Mat)‖
  have hr : 0 < r := by unfold r; positivity
  have hb : ∀ y∈ball (physical (U x)) r, ‖f y‖ ≤ m := by
    intro y hy
    apply (stringMat_bound _ hr.le _ (ball_subset_closedBall hy) _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      (1+r)^w.length ≤ (Real.exp r)^w.length := pow_le_pow_left₀ (by linarith) (by rw [add_comm]; exact Real.add_one_le_exp r) _
      _ ≤ _ := by
        rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
        unfold r; rw [← div_eq_mul_inv]; apply (div_le_one (by positivity)).2
        exact (show (w.length:ℝ) ≤ a by exact_mod_cast ha).trans (le_add_of_nonneg_left zero_le_one)
  have hh := allows_real_of_entire N (stringMat_contDiff w s) hr hb
  simp_rw [← stringMat_physical,travelCost]
  have he : (2:ℝ)^N/r=2^N*(1+a) := by rw [div_eq_mul_inv]; simp only [r,inv_inv]
  rw [he] at hh
  exact hh.comp (f:=fun y => physical (U y)) (allows_ambient h)

lemma allows_average {ι : Type*} [Fintype ι] [Nonempty ι] {f : ι → E → ℝ}
    (h : ∀ i, Allows N (f i) x C) : Allows N (fun y => Patch.average (fun i => f i y)) x C := by
  let m : ℝ := Fintype.card ι
  have hm : 0 < m := by unfold m; positivity
  have he := (allows_sum (s:=Finset.univ) fun i _ => h i).smul m⁻¹
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, abs_of_nonneg (inv_pos.mpr hm).le] at he
  rwa [show (Fintype.card ι:ℝ) = m from rfl, inv_mul_cancel_left₀ hm.ne'] at he
end YM.Push.Uniform
