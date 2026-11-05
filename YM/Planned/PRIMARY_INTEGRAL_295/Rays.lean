import YM.Planned.PRIMARY_INTEGRAL_295.Carrier


/-!
# Directional Laurent-moment identity, before using the flat kernel

Pre-side analytic strip mass supplies absolute estimates for every finite
polynomial order. Work along an actual *real* momentum line; these tests
will suffice by polarization. Do not drop harmonic mode or apply statements
about torus contour on the physical field insertion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Carrier
open Function Filter Lattice Laurent Bloch Precision RG Next.Free Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {L : Side} {j t : ℕ}

abbrev RouteProbe := E4 →L[ℝ] ℝ

def ray (w : RouteProbe) (t : ℝ) : Momentum := fun i => (t*w (basis i) : ℝ)

def tune (r t : ℝ) : ℂ := Complex.exp (↑(r*t)*Complex.I)

lemma ray_smooth (w : RouteProbe) : ContDiff ℝ ω (ray w) := by
  apply contDiff_pi.mpr; intro i; exact Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const)
lemma ray_root (w : RouteProbe) : ray w 0=0 := by ext; simp [ray]
lemma ray_live (w : RouteProbe) (t : ℝ) : physical (ray w t) := by
  rw [physical_iff]; intro i; exact Complex.ofReal_im _
lemma ray_in (w : RouteProbe) : ∀ᶠ t : ℝ in 𝓝 0, ray w t∈baseCube := by
  have he (i : Axis) : ∀ᶠ t in 𝓝 (0:ℝ), |(ray w t i).re| ≤ Real.pi := by
    have ht : Continuous (fun t => |(ray w t i).re|) := by unfold ray; fun_prop
    refine (ht.tendsto 0).eventually (ge_mem_nhds ?_); rw [ray_root]; simpa using Real.pi_pos
  filter_upwards [eventually_all.mpr he] with t ht
  exact ⟨ray_live ..,ht⟩
lemma tune_one (r : ℝ) : tune r 0=1 := by simp [tune]
lemma tune_norm (r t : ℝ) : ‖tune r t‖ = 1 := by simp only [tune, Complex.norm_exp]; simp
lemma tune_add (r q t : ℝ) : tune (r+q) t=tune r t*tune q t := by
  unfold tune; rw [add_mul, Complex.ofReal_add,add_mul,Complex.exp_add]
lemma through_mode (w : RouteProbe) (t : ℝ) (x : Cover) : mode (ray w t) x = tune (w (seat x)) t := by
  unfold mode ray tune; apply congr_arg
  conv_rhs => rw [← show ∑ i : Axis, seat x i • basis i = seat x from by ext i; simp]
  simp only [_root_.map_sum,map_smul,seat_apply,smul_eq_mul,Finset.sum_mul,Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; push_cast; ring
lemma narrow_mode (w : RouteProbe) (t : ℝ) (x : Cover) (L : Side) :
    mode (aliasAt (ray w t) (0:Site L)) x=tune (w ((L.val:ℝ)⁻¹ • seat x)) t := by
  rw [alias_zero_eq (M:=L)]
  have he : narrow L (ray w t)=ray w ((L.val:ℝ)⁻¹*t) := by
    funext i; rw [narrow_apply]; unfold ray; push_cast; ring
  rw [he,through_mode,map_smul]
  unfold tune; change Complex.exp _ = Complex.exp _
  congr 2; simp [mul_comm,mul_assoc]

lemma tune_derivative (r t : ℝ) : HasDerivAt (tune r) (↑r * Complex.I * tune r t) t := by
  have he : HasDerivAt (fun t : ℝ => ((r*t:ℝ):ℂ)) (r:ℂ) t := by
    have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).const_mul r)
    simpa only [mul_one] using! hc
  unfold tune; exact ((he.mul_const Complex.I).cexp).congr_deriv (by ring)

private def impulse (w : RouteProbe) (a : E4) (q : Cover → ℝ) (n : ℕ) (z : Cover) (t : ℝ) : ℂ :=
  let r : ℝ := w (a+seat z)
  (r*Complex.I)^n * tune r t * (q z:ℂ)

private lemma impulse_norm (w : RouteProbe) (a : E4) (q : Cover → ℝ) (n : ℕ) (z : Cover) (t : ℝ) :
    ‖impulse w a q n z t‖ = ‖q z‖ * ‖w (a+seat z)‖^n := by
  unfold impulse; simp only [Complex.norm_pow,norm_mul,tune_norm,Complex.norm_I, Complex.norm_real,mul_one]; exact mul_comm ..

private lemma impulse_sums (w : RouteProbe) (a : E4) (n : ℕ) {q : Cover → ℝ} {σ C : ℝ}
    (hσ : 0<σ) (h : Width σ C q) (t : ℝ) : Summable (fun z => ‖impulse w a q n z t‖) := by
  have he := width_income hσ h n
  let p := 1 + ‖w‖ * (1+‖a‖)
  have hp (z : Cover) : ‖w (a+seat z)‖ ≤ p*(1+size z) := by
    apply (w.le_opNorm _).trans
    have he := add_le_add_right (shade_seat z) ‖a‖
    apply (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans he) (norm_nonneg _)).trans
    unfold p; nlinarith [norm_nonneg w,norm_nonneg a,Nat.cast_nonneg (α:=ℝ) (size z),mul_nonneg (mul_nonneg (norm_nonneg w) (norm_nonneg a)) (Nat.cast_nonneg (α:=ℝ) (size z))]
  apply (he.2.1.mul_left (p^n)).of_nonneg_of_le (fun _ => norm_nonneg _); intro i
  rw [impulse_norm]; apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hp i) n) (norm_nonneg _)).trans_eq
  unfold liftCost; rw [mul_pow,mul_left_comm]

def pulseAt (w : RouteProbe) (a : E4) (q : Cover → ℝ) (t : ℝ) := ∑' z, tune (w (a+seat z)) t * (q z:ℂ)

lemma pulse_lift (w : RouteProbe) (a : E4) (q : Cover → ℝ) (t : ℝ) :
    pulseAt w a q t=tune (w a) t * RRead q (ray w t) := by
  unfold pulseAt RRead Laurent.read; rw [← tsum_mul_left]; refine tsum_congr fun i => ?_
  rw [through_mode,map_add,tune_add,mul_assoc]; rfl

private lemma pulse_side (w : RouteProbe) (a : E4) (n : ℕ) {q : Cover → ℝ} {σ C : ℝ} (hσ : 0 < σ)
    (h : Width σ C q) : iteratedDeriv n (pulseAt w a q) =(fun t => ∑' z, impulse w a q n z t) := by
  classical
  induction n with
  | zero => funext t; simp [pulseAt, impulse]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]; funext t
    let u := impulse w a q
    have hd (z s) : HasDerivAt (u n z) (u (n+1) z s) s := by
      let r := w (a+seat z)
      unfold u impulse
      apply (((tune_derivative r s).const_mul _).mul_const _).congr_deriv
      unfold r; dsimp only; ring
    exact (hasDerivAt_tsum (impulse_sums w a (n+1) hσ h 0) hd
      (fun z s => le_of_eq (by unfold u;rw [impulse_norm,impulse_norm]))
      ((impulse_sums w a n hσ h 0).of_norm) t).deriv

/-- The actual (unnormalized) derivative order n, in initial-vertex
coordinates, translated by ANY continuous origin a. -/
lemma moment_probe (w : RouteProbe) (a : E4) (n : ℕ) {q : Cover → ℝ} {σ C : ℝ} (hσ : 0<σ) (h : Width σ C q) :
    iteratedDeriv n (pulseAt w a q) 0 = Complex.I^n * ((∑' z, (w (a+seat z))^n*q z : ℝ) : ℂ) := by
  rw [pulse_side w a n hσ h, Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun i => ?_; unfold impulse; simp only [tune_one, mul_one, Complex.ofReal_mul, Complex.ofReal_pow]; ring

end YM.Planned.PrimaryIntegral295.Carrier
