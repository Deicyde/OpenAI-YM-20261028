import YM.Extra.FREE_DETECTOR_ALGEBRA.CurlDetect

set_option warningAsError false

/-!
# Kelvin formula incl coefficient of each tensor dual

Normalized result for response at `x-y`. Next step will use covariance and
translation of these Kelvin transforms to get nonsingularity AND positivity
in each finite grade. No momentum cutoffs or contacts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {G : Gauge} {j : ℕ} {x : E4}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Contraction with the radius vector. -/
def radialP (S : Sol F j) (i : Axis) (x : E4) : F := ∑ a : Axis, x a • S.field a i x

theorem radial_smooth (S : Sol F j) (i : Axis) (x : E4) : ContDiffAt ℝ ∞ (radialP S i) x := by
  unfold radialP
  exact ContDiffAt.sum fun a _ => (compAxis a).contDiff.contDiffAt.smul (S.smooth _ _ _)

theorem radial_curl (S : Sol F j) (i m : Axis) (x : E4) :
    grad i (radialP S m) x - grad m (radialP S i) x = ((j+2 : ℕ) : ℝ) • S.field i m x := by
  have he (a i) : grad a (radialP S i) x = S.field a i x + ∑ b : Axis, x b • grad a (S.field b i) x :=
    grad_self (fun b => S.val b i) a x
  have ht (a b) : S.field a b = -S.field b a := funext fun y => S.wave.form _ _ y (mem_univ _)
  have hc (a) : grad i (S.field a m) x - grad m (S.field a i) x = grad a (S.field i m) x := by
    have hv := S.wave.cycle i a m x (mem_univ _)
    rw [ht m i, grad_neg_f, ht i a, grad_neg_f] at hv
    rw [← add_right_cancel_iff (a := (-grad a (S.field i m) x))]
    exact ((show grad i (S.field a m) x - grad m (S.field a i) x + -grad a (S.field i m) x =
        grad i (S.field a m) x + -grad a (S.field i m) x + -grad m (S.field a i) x by abel).trans hv).trans (by simp)
  have heuler : ∑ a : Axis, x a • grad a (S.field i m) x = (j:ℝ) • S.field i m x := grad_euler _ (S.closed.coeffSym i m) x
  rw [he,he,add_sub_add_comm,← Finset.sum_sub_distrib]
  simp_rw [← smul_sub,hc,heuler]
  rw [ht m i,Pi.neg_apply,sub_neg_eq_add, ← two_smul ℝ, ← add_smul]
  congr 1
  push_cast; ring

def strength (j : ℕ) : ℝ := 4 * (j+1) * (j+2) * (-2)^j * normal

theorem strength_ne (j : ℕ) : strength j ≠ 0 := by
  unfold strength; have h := normal_pos; positivity

theorem strength_sign (j : ℕ) : 0 < (-1:ℝ)^j * strength j := by
  unfold strength
  rw [mul_comm _ normal, mul_left_comm]
  have he : (-1:ℝ)^j * (4 * (↑j + 1) * (↑j + 2) * (-2)^j) = 4 * (↑j+1) * (↑j+2) * 2^j := by rw [mul_left_comm, ← mul_pow]; norm_num
  rw [he]; have h := normal_pos; positivity

/-- Off-origin `divP` reduces to a simple homogeneous radial product on
shell, because divergence on the tensor itself vanishes. -/
theorem divP_value (S : Sol F j) (hx : x ∈ away) (i : Axis) :
    divP S i x = ((-2)^j * normal * (-(2*((j+1:ℕ):ℝ))) * rr x ^ (j+2)) • radialP S i x := by
  let R : E4 → ℝ := rr ^ (j+1)
  let c : ℝ := (-2)^j * normal
  let d : ℝ := -(2*((j+1:ℕ):ℝ)) * rr x ^ (j+2)
  have hr : ContDiffAt ℝ ∞ R x := (rr_smooth hx).pow _
  have hd (a : Axis) : grad a R x = d * x a := grad_power hx _ a
  have he (a : Axis) : applyDiff (S.val a i) Green =ᶠ[𝓝 x] (c • (R • S.field a i)) := by
    filter_upwards [open_away.mem_nhds hx] with y hy
    have hy : applyDiff (S.val a i) Green y = (c * R y) • S.field a i y := shell_green S hy a i
    rw [hy,mul_smul]; rfl
  have ht (a : Axis) : grad a (applyDiff (S.val a i) Green) x = c •
      (d • (x a • S.field a i x) + R x • grad a (S.field a i) x) := by
    rw [show grad a _ x = grad a (c • (R • S.field a i)) x from GermD _ (he a),
      grad_smul (show ContDiffAt ℝ ∞ (R • S.field a i) x from hr.smul (S.smooth a i x)), grad_times hr (S.smooth a i x),hd,mul_smul d]
  unfold divP
  simp_rw [ht, ← Finset.smul_sum, Finset.sum_add_distrib, ← Finset.smul_sum,S.wave.divergence i x (mem_univ _),smul_zero,add_zero]
  change c • d • radialP S i x = _
  rw [smul_smul]; dsimp only [c,d]; rw [mul_assoc ((-2)^j*normal)]

def reflectedF (S : Sol F j) (i m : Axis) (x : E4) : F :=
    S.field i m x - (2*rr x) • (x i • radialP S m x - x m • radialP S i x)

theorem curl_kelvin (S : Sol F j) (hx : x ∈ away) (i m : Axis) :
    ∑ a : Axis, ∑ b : Axis, applyDiff (S.val a b) (bareCurl a b i m) x =
      (strength j * rr x ^ (j+2)) • reflectedF S i m x := by
  rw [curl_reduce S hx]
  let c : ℝ := (-2)^j * normal * (-(2*((j+1:ℕ):ℝ)))
  let R : E4 → ℝ := rr ^ (j+2)
  have hr : ContDiffAt ℝ ∞ R x := (rr_smooth hx).pow _
  let t : ℝ := ↑(j+2:ℕ)
  let d := (-(2*t))* rr x^(j+3)
  have hd (a : Axis) : grad a R x = d * x a := grad_power hx _ a
  have he (i : Axis) : divP S i =ᶠ[𝓝 x] (c • (R • radialP S i)) := by
    filter_upwards [open_away.mem_nhds hx] with y hy
    have hy : divP S i y = (c * R y) • radialP S i y := divP_value S hy i
    rw [hy,mul_smul]; rfl
  have ht (a i : Axis) : grad a (divP S i) x = c • (d • (x a • radialP S i x) + R x • grad a (radialP S i) x) := by
    rw [show grad a (divP S i) x = grad a (c • (R • radialP S i)) x from GermD _ (he i),
      grad_smul (show ContDiffAt ℝ ∞ (R • radialP S i) x from hr.smul (radial_smooth S i x)),grad_times hr (radial_smooth S i x),hd,mul_smul d]
  rw [ht,ht,← smul_sub,add_sub_add_comm,← smul_sub,← smul_sub,← neg_sub (a := grad i (radialP S m) x),radial_curl]
  let V : F := x i • radialP S m x - x m • radialP S i x
  change (2:ℝ) • c • (d • _ + R x • -(t • S.field i m x)) = (strength j * R x) • (S.field i m x - (2*rr x) • V)
  rw [← neg_sub (a:= x i • radialP S m x)]
  have hk : (-(2*c*t))=strength j := by unfold strength; dsimp only [c,t]; push_cast; ring
  have hd : d = -(2*t)*R x*rr x := by
    change _ = -(2*t)*rr x^(j+2)*rr x
    rw [mul_assoc,← pow_succ]
  change (2:ℝ) • c • (d • -V + R x • -(t • S.field i m x)) = _
  rw [hd, ← hk]
  module

theorem reply_kelvin (S : Sol G.Color j) (hx : x ∈ away) (i m : Axis) :
    reply (G:=G) S i m x = (strength j * rr x ^ (j+2)) • reflectedF S i m x :=
  (replyFrob S hx i m).trans (curl_kelvin S hx i m)
end YM.Extra.FD
