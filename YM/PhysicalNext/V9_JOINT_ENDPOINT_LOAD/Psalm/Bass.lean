import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Double

/-! # Signs and products for the singleton (before the linear negative-log
and derivative comparison recurrence). Scale E by λ, uniform including the
two comparison endpoints; don't read that as varying the retained vacuum
labels, and no replacing the stochastic procedure. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm.Solo
open Filter Function Set Lattice Wilson RG Tree Pressure Precision Bid Next.SectorChange ProjectorNext.Equivariance
    Heir AnalyticBridge.LocalGaussian AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {n : ℕ} {θ τ v K : ℝ} {H : ℝ → ℝ → ℝ}

lemma Marked.const_mul (h : Marked H n K) (a : ℝ) : Marked (fun γ x => a*H γ x) n (|a| *K) := by
  refine ⟨⟨?_,fun γ => contDiff_const.mul (h.each γ), fun γ => by rw [h.flat,mul_zero],fun γ => ?_⟩, fun {f G} V F test {τ} hτ he γ hγ => ?_⟩
  · simp_rw [mul_left_comm (b:=a)]; exact contDiff_const.mul h.joint
  · exact ((hasFDerivAt_const ..).mul (show HasFDerivAt (H γ) (fderiv ℝ (H γ) 0) 0 from ((h.each γ).differentiable (by simp) 0).hasFDerivAt)).fderiv.trans (by simp [h.quiet])
  rw [mul_assoc]; exact (h.fees V F test hτ he γ hγ).indiv a

lemma Wholesome.grow (h : Wholesome H) (θ : ℝ) : Wholesome (fun γ x => Real.exp (γ*θ*x)*H γ x) := by
  refine ⟨by simp_rw [mul_left_comm _ (Real.exp _)]; exact ((contDiff_fst.mul contDiff_const).mul contDiff_snd).exp.mul h.joint,
    fun γ => ((contDiff_const.mul contDiff_id).exp).mul (h.each γ),fun γ => by rw [h.flat, mul_zero], fun γ => ?_⟩
  exact ((show Differentiable ℝ (fun x : ℝ => Real.exp (γ*θ*x)) by fun_prop).differentiableAt.hasFDerivAt.mul
    (show HasFDerivAt (H γ) (fderiv ℝ (H γ) 0) 0 from ((h.each γ).differentiable (by simp) 0).hasFDerivAt)).fderiv.trans (by simp [h.quiet,h.flat])

def raised (n : ℕ) := Real.exp 1 *(climbing n 2+1)^n
lemma raised_pos (n : ℕ) : 0 < raised n := by unfold raised; positivity [climbing_nonneg n zero_le_two]
lemma Marked.raised (h : Marked H n K) (hθ : |θ| ≤ 1) : Marked (fun γ x => Real.exp (γ*θ*x)*H γ x) n (Solo.raised n *K) := by
  refine ⟨h.toWholesome.grow θ,fun {f G} V F test {τ} hτ he γ hγ => ?_⟩
  have hw : ‖γ*θ‖ * τ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ (mul_le_one₀ hγ (abs_nonneg _) hθ) he.price_nonneg hτ
  have ht := ((he.indiv (γ*θ)).mono hw le_rfl)
  obtain hh := ((ht.tip.bill_exp (Real.exp_monotone ((le_abs_self _).trans ht.base))).mul (h.fees _ _ _ hτ he γ hγ))
  rw [one_add_one_eq_two,mul_one] at hh
  apply (unitize (le_add_of_nonneg_left (climbing_nonneg n zero_le_two)) hh).mono (le_of_eq _) le_rfl
  unfold Solo.raised; ring

def halfPrice (x : ℝ) := 1-Real.exp x+x
def tiltPrice (x : ℝ) := x*(Real.exp x-1)

def bass (θ : ℝ) := transform halfPrice (-θ)
def drone (θ γ x : ℝ) := (-θ)⁻¹ * transform tiltPrice (-θ) γ x
def chime (θ v γ x : ℝ) := Real.exp (γ*(-θ)*x)*bass v γ x




lemma Marked.higher (h : Marked H n K) (hv : K ≤ v) : Marked H n v := ⟨h.toWholesome, fun {f G} V F test {τ} ht h' γ hγ => (h.fees V F test ht h' γ hγ).mono (by gcongr) le_rfl⟩
structure Instrument (n : ℕ) where
  bid : ℝ
  large : 1 ≤ bid
  main (θ : ℝ) : |θ| ≤ 1 → Marked (bass θ) n bid
  shift (θ : ℝ) : |θ| ≤ 1 → Marked (drone θ) n bid
  change (θ s : ℝ) : |θ| ≤ 1 → |s| ≤ 1 → Marked (chime θ s) n (bid*s^2)

lemma instrument (n : ℕ) : Nonempty (Instrument n) := by
  obtain ⟨K,hK,hk⟩ := double halfPrice (by unfold halfPrice; fun_prop) (by simp [halfPrice]) (by
    exact (((hasDerivAt_const ..).sub (Real.hasDerivAt_exp _)).add (hasDerivAt_id' _)).hasFDerivAt.fderiv.trans (by simp)) n
  obtain ⟨L,hL,h⟩ := double tiltPrice (by unfold tiltPrice; fun_prop) (by simp [tiltPrice]) (by
    exact ((hasDerivAt_id' _).mul ((Real.hasDerivAt_exp _).sub_const 1)).hasFDerivAt.fderiv.trans (by simp)) n
  have hhw := raised_pos n; have he θ (h : |θ| ≤ (1:ℝ)) : K*(-θ)^2 ≤ K := by have hh := abs_le.mp h; nlinarith [mul_nonneg (a:=1-θ^2) (by nlinarith) hK]
  let M := 1+K+L+Solo.raised n * K; have hM : 1≤M := by unfold M; nlinarith
  refine ⟨M,hM,fun θ hθ => (hk (-θ) ((abs_neg _).trans_le hθ)).higher ((he θ hθ).trans ?_),fun θ hθ => ((h (-θ) ((abs_neg _).trans_le hθ)).const_mul _).higher ?_,
    fun θ s hθ hs => ((hk (-s) ((abs_neg _).trans_le hs)).raised ((abs_neg _).le.trans hθ)).higher ?_⟩
  · unfold M; nlinarith only [hL,mul_nonneg hhw.le hK]
  · unfold M; rw [abs_inv]; by_cases hh : -θ=0; · simp [hh]; nlinarith
    apply le_trans (b:=L) ?_ (by nlinarith only [mul_nonneg hhw.le hK,hK]); rw [inv_mul_le_iff₀ (abs_pos.mpr hh),← sq_abs]
    nlinarith only [mul_le_mul_of_nonneg_left ((abs_neg θ).le.trans hθ) (mul_nonneg hL (abs_nonneg (-θ)))]
  rw [even_two.neg_pow,←mul_assoc]; unfold M; gcongr ?_ * _; linarith only [hK,hL]
end YM.PhysicalNext.JointLoad.Psalm.Solo
