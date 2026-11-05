import YM.Extra.FREE_DETECTOR_ALGEBRA.Harmonic
import YM.Maxwell.Bilinear

set_option warningAsError false

/-! Kelvin response of a tensor dual to the actual curled covariance.
Both derivatives differentiating x initially, z=x-y. The sign for
second-side potentials is already in `curlOpp` (do not also negate the
base contraction!); for high jet tests **at y** use the additional `(-1)^l`
as in `legKernel`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Set Filter Tensor Analysis Maxwell
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {G : Gauge} {j l : ℕ} {x : E4}
local notation "Csol" => Sol G.Color

/-- Specific extension of the one-leg probe `dualSol _ _ P`; the actual
kernel is independent of this choice off the origin. -/
def direct (P : Sol G.Color j) : Maxwell.Extended G j := dotF P.val

def reply (P : Sol G.Color j) : Maxwell.Field G.Color := responded G (direct P)

theorem replied (P : Sol G.Color j) : WaveOn away (reply (G:=G) P) := response (G:=G) _

theorem replyTest (P : Sol G.Color j) (Q : Sol G.Color l) (hx : x ∈ away) :
    legKernel (G:=G) (dualSol G.Color _ P) (dualSol G.Color _ Q) x =
      (-1)^l * dotF Q.val (WaveOn.nth (reply (G:=G) P) l x) :=
  concrete (direct P) (direct Q) hx

private theorem inner_unit (v : G.Color) (c : G.ColorIndex) : ⟪v,unitColor G c⟫ = v c := by
  rw [PiLp.inner_apply]; simp [unitPaint, RCLike.inner_apply]

theorem replyFrob (P : Sol G.Color j) (hx : x ∈ away) (i m : Axis) :
    reply (G := G) P i m x = ∑ a : Axis, ∑ b : Axis, applyDiff (P.val a b) (bareCurl a b i m) x := by
  ext1 c
  rw [reply, observed]
  change dotF P.val (WaveOn.nth _ j x) = _
  have he (a b : Axis) (u : Fin j → E4) :
      WaveOn.nth (leftF G c i m) j x a b u = tint (unitColor G c) (coeff (bareCurl a b i m) j x u) :=
    coeff_linear (tint (unitColor G c)) u ((Bare.curl_diff hx a b i m).of_le (WithTop.coe_le_coe.mpr le_top))
  simp_rw [dotF_eval,dotDir_eval,applyDiff, he,tint_at,real_inner_smul_right,inner_unit]
  simp

section calculus
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
private lemma apDiff_neg (P : T E4 F j) (f : E4 → ℝ) :
    applyDiff (-P) f = -applyDiff P f := by funext y; simp [applyDiff, Finset.sum_neg_distrib]
private lemma apDiff_sub {f g : E4 → ℝ} (P : T E4 F j) (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    applyDiff P (f-g) x = applyDiff P f x - applyDiff P g x := by
  have he (f g : E4 → ℝ) : f-g=f+-g := sub_eq_add_neg f g
  have hn : ContDiffAt ℝ ∞ (-g) x := hg.neg
  rw [applyDiff,he,coeff_add (hf.of_le (WithTop.coe_le_coe.mpr le_top)) (hn.of_le (WithTop.coe_le_coe.mpr le_top)),neg_coeff]
  simp [applyDiff,sub_eq_add_neg,Finset.sum_add_distrib, Finset.sum_neg_distrib,add_smul]

private lemma op_choose (P : T E4 F j) (hx : x ∈ away) (b i m : Axis) :
    applyDiff P (curlOpp b i m) x =
      (if i=b then grad m (applyDiff P Green) x else 0) - if m=b then grad i (applyDiff P Green) x else 0 := by
  rw [curlOpp,apDiff_sub P (Bare.choose_diff hx b m i) (Bare.choose_diff hx b i m), deriv_applyDiff _ (freeSmooth hx),
    deriv_applyDiff _ (freeSmooth hx)]
  have he : applyDiff P (0:E4→ℝ) x = 0 := by simp [applyDiff,coeff]
  split_ifs <;> simp_all

lemma op_grad (P : T E4 F j) (hx : x ∈ away) (a b i m : Axis) :
    grad a (applyDiff P (curlOpp b i m)) x =
      (if i=b then grad m (grad a (applyDiff P Green)) x else 0) - if m=b then grad i (grad a (applyDiff P Green)) x else 0 := by
  have he : applyDiff P (curlOpp b i m) =ᶠ[𝓝 x]
      ((if i=b then grad m (applyDiff P Green) else 0) - if m=b then grad i (applyDiff P Green) else 0) := by
    filter_upwards [open_away.mem_nhds hx] with y hy
    rw [op_choose P hy]; split_ifs <;> rfl
  have hg := smooth_applyDiff P (freeSmooth hx)
  have hd (c d) : ContDiffAt ℝ ∞ (if c=b then grad d (applyDiff P Green) else 0) x := by
    split_ifs; exact grad_smooth_at hg d; exact contDiffAt_const
  have hh {f g : E4 → F} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
      grad a (f-g) x = grad a f x - grad a g x := by
    unfold grad D; rw [fderiv_sub (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp))]; rfl
  unfold grad
  rw [GermD _ he]
  change grad a _ x = (if i=b then grad m (grad a (applyDiff P Green)) x else 0)-if m=b then grad i (grad a (applyDiff P Green)) x else 0
  rw [hh (hd i m) (hd m i)]
  have hz : grad a (0:E4→F) x = 0 := by simp [grad,D]
  split_ifs <;> first | rfl | (simp only [hz,grad_exchange hg a i,grad_exchange hg a m])

/-- Contraction of the probe with uncurled scalar Green; take the divergence
in first form index. -/
def divP (S : Sol F j) (i : Axis) (y : E4) : F := ∑ a : Axis, grad a (applyDiff (S.val a i) Green) y

theorem curl_reduce (S : Sol F j) (hx : x ∈ away) (i m : Axis) :
    ∑ a : Axis, ∑ b : Axis, applyDiff (S.val a b) (bareCurl a b i m) x =
      (2:ℝ) • (grad m (divP S i) x - grad i (divP S m) x) := by
  let V := fun a b => grad a (applyDiff (S.val a b) (curlOpp b i m)) x
  have he (a b) : applyDiff (S.val a b) (bareCurl a b i m) x = V a b + V b a := by
    obtain hg := Bare.opp_diff hx b i m; obtain ht := Bare.opp_diff hx a i m
    rw [bareCurl, apDiff_sub _ (grad_smooth_at hg _) (grad_smooth_at ht _), ← deriv_applyDiff _ hg, ← deriv_applyDiff _ ht]
    dsimp only [V]
    nth_rw 2 [S.closed.antisymmetric a b]
    rw [apDiff_neg,grad_neg_f,sub_neg_eq_add]
  have hv : ∑ a : Axis, ∑ b : Axis, V a b = grad m (divP S i) x - grad i (divP S m) x := by
    have ht (a) : ∑ b : Axis, V a b = grad m (grad a (applyDiff (S.val a i) Green)) x -
        grad i (grad a (applyDiff (S.val a m) Green)) x := by
      unfold V; simp_rw [fun b => op_grad (S.val a b) hx a b i m, Finset.sum_sub_distrib]; simp
    simp_rw [ht, Finset.sum_sub_distrib]
    unfold divP
    have hd (a b) := grad_smooth_at (smooth_applyDiff (S.val a b) (freeSmooth hx)) a
    rw [grad_sum_fun _ (fun a _ => hd a i),grad_sum_fun _ (fun a _ => hd a m)]
  simp_rw [he,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => V b a),hv,two_smul]
end calculus
end YM.Extra.FD
