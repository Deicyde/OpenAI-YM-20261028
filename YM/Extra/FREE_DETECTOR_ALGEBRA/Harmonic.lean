import YM.Analysis.Exchange
import YM.Extra.FREE_DETECTOR_ALGEBRA.Frobenius
import YM.Maxwell.Leg

set_option warningAsError false

/-!
# Harmonic directional tensors applied to the 4D Green function

For the reflected detector we will use a Kelvin-transform formula instead of
needing any Fourier / distributional hypothesis on either hierarchy. All
statements off coincidence.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {j : ℕ}
variable {x : E4}

/-- Reciprocal squared radius. -/
def rr (x : E4) : ℝ := (‖x‖^2)⁻¹

lemma rr_pos (hx : x ∈ away) : 0 < rr x := by have he := norm_pos_iff.mpr hx; unfold rr; positivity
lemma rr_smooth (hx : x ∈ away) : ContDiffAt ℝ ∞ rr x := by
  have he := norm_pos_iff.mpr hx; exact (contDiff_norm_sq ℝ).contDiffAt.inv (by dsimp; positivity)
lemma grad_rr (hx : x ∈ away) (i : Axis) : grad i rr x = -2 * x i * rr x^2 := by
  have he := norm_pos_iff.mpr hx
  have h := (hasFDerivAt_inv (show ‖x‖^2 ≠ 0 by positivity)).comp x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  unfold grad D rr
  change fderiv ℝ ((fun y : ℝ => y⁻¹) ∘ fun x : E4 => ‖x‖^2) x _ = _
  rw [h.fderiv]; simp [two_smul]
  rw [← real_inner_comm x, basis_inner]; ring

lemma grad_power (hx : x ∈ away) (k : ℕ) (a : Axis) :
    grad a (rr^k) x = - (2*(k : ℝ)) * rr x ^ (k+1) * x a := by
  unfold grad D
  rw [fderiv_pow _ ((rr_smooth hx).differentiableAt (by simp)),smul_apply]
  change (k • rr x ^ (k-1)) * grad a rr x = _
  rw [grad_rr hx]
  cases k with
  | zero => simp
  | succ j => push_cast; simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one,pow_succ]; ring

lemma grad_times {f : E4 → ℝ} {g : E4 → F} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (a : Axis) :
    grad a (f • g) x = grad a f x • g x + f x • grad a g x := by
  unfold grad D
  rw [((hf.differentiableAt (by simp)).hasFDerivAt.smul (hg.differentiableAt (by simp)).hasFDerivAt).fderiv]
  exact add_comm ..

lemma grad_sum_fun {ι : Type*} (s : Finset ι) {f : ι → E4 → F} (hf : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) (a : Axis) :
    grad a (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, grad a (f i) x := by
  unfold grad D; rw [fderiv_fun_sum (fun i hi => (hf i hi).differentiableAt (by simp)),sum_apply]

/-- Normalized derivative symbol applied to a scalar function. Directions
sum over ordered tuples, `coeff` means actual Taylor coefficient. -/
def applyDiff (P : T E4 F j) (f : E4 → ℝ) (x : E4) : F :=
    ∑ v : Dirs j, (coeff f j x (dir v)) • P (dir v)

theorem ap_const {f : E4 → ℝ} (P : T E4 F 0) (y : E4) (v : Fin 0 → E4) :
    applyDiff P f y = f y • P v := by
  simp only [applyDiff,coeff_apply_zero]
  simp_rw [show ∀ w : Dirs 0, dir w = v from fun _ => Subsingleton.elim ..]
  simp

theorem coeff_dirs {f : E4 → ℝ} (hf : ContDiffAt ℝ ∞ f x) (v : Dirs j) :
    ContDiffAt ℝ ∞ (fun y => coeff f j y (dir v)) x :=
  (ContinuousMultilinearMap.apply ℝ (fun _ => E4) ℝ (dir v)).contDiff.contDiffAt.comp x (coeff_smooth hf j)

theorem smooth_applyDiff {f : E4 → ℝ} (P : T E4 F j) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (applyDiff P f) x :=
  ContDiffAt.sum (s := Finset.univ) (f := fun v y => coeff f j y (dir v) • P (dir v))
    (fun i _ => (coeff_dirs hf i).smul contDiffAt_const)

theorem deriv_applyDiff {f : E4 → ℝ} (P : T E4 F j) (hf : ContDiffAt ℝ ∞ f x) (a : Axis) :
    grad a (applyDiff P f) x = applyDiff P (grad a f) x := by
  unfold applyDiff
  let E (v : Dirs j) (y) := coeff f j y (dir v)
  have he v : grad a (E v) x = coeff (grad a f) j x (dir v) := by
    let L := ContinuousMultilinearMap.apply ℝ (fun _ => E4) ℝ (dir v)
    change grad a (L ∘ fun y => coeff f j y) x = _
    rw [grad_linear L (coeff_smooth hf _)]
    exact congr_arg L (D_coeff (hf.of_le (WithTop.coe_le_coe.mpr le_top)) (basis a))
  let T (v : Dirs j) (y : E4) := E v y • P (dir v)
  have ht (v : Dirs j) : ContDiffAt ℝ ∞ (T v) x := (coeff_dirs hf v).smul contDiffAt_const
  change grad a (fun y => ∑ v, T v y) x = _
  rw [grad_sum_fun _ (fun i _ => ht i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← he]
  unfold grad D T
  rw [fderiv_smul_const (show DifferentiableAt ℝ (E i) x from (coeff_dirs hf i).differentiableAt (by simp))]
  rfl

theorem applyDiff_succ {f : E4 → ℝ} (P : T E4 F (j+1)) (hf : ContDiffAt ℝ ∞ f x) :
    applyDiff P f x = ((↑(j+1:ℕ):ℝ))⁻¹ •
      ∑ a : Axis, grad a (applyDiff (P.curryLeft (basis a)) f) x := by
  simp_rw [fun a => deriv_applyDiff (P.curryLeft (basis a)) hf a]
  unfold applyDiff; rw [sum_dirs]
  simp_rw [dir_cons,ContinuousMultilinearMap.curryLeft_apply,
    coeff_apply_cons (hf.of_le (show ((↑(j+1 : ℕ)) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)), Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by change (_*_ : ℝ) • _ = _; rw [mul_smul]; rfl

theorem axis_resolve (x : E4) : ∑ a : Axis, x a • basis a = x := by
  apply PiLp.ext; intro i; simp

theorem freeze_diagonal (S : Sol F (j+1)) (i m : Axis) (x : E4) :
    ∑ a : Axis, x a • (Sol.freeze S a).field i m x = S.field i m x := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => E4) F (fun _ => x) |>.comp (S.val i m).curryLeft
  have he : L x = S.field i m x := by
    change S.val i m (Fin.cons x (fun _ => x)) = _
    rw [show Fin.cons x (fun _ : Fin j => x) = fun _ => x by ext1 h; refine Fin.cases ?_ (fun _ => ?_) h <;> rfl]
    rfl
  rw [← he]
  have ht := congr_arg L (axis_resolve x)
  rw [map_sum] at ht; simp_rw [map_smul] at ht
  exact ht

/-- Kelvin contraction with the 4D Green function. -/
theorem shell_green (S : Sol F j) (hx : x ∈ away) (i m : Axis) :
    applyDiff (S.val i m) Green x = ((-2)^j * normal * rr x ^ (j+1)) • S.field i m x := by
  induction j generalizing x with
  | zero => rw [ap_const (S.val i m) x (fun _ => x)]; simp only [pow_zero,one_mul,zero_add,pow_one]; rfl
  | succ j ih =>
    rw [applyDiff_succ _ (freeSmooth hx)]
    let c : ℝ := (-2)^j * normal
    let Q (a : Axis) := Sol.freeze S a
    let R : E4 → ℝ := rr^(j+1)
    have hr : ContDiffAt ℝ ∞ R x := ((rr_smooth hx).pow _)
    have he (a : Axis) : applyDiff ((S.val i m).curryLeft (basis a)) Green =ᶠ[𝓝 x]
        (c • (R • (Q a).field i m)) := by
      filter_upwards [open_away.mem_nhds hx] with y hy
      have ht : applyDiff ((S.val i m).curryLeft (basis a)) Green y = (c * R y) • (Q a).field i m y := ih (Q a) hy
      rw [ht,mul_smul]; rfl
    let n : ℝ := ↑(j+1:ℕ)
    let d : ℝ := -(2*n) * rr x ^ (j+2)
    have ht (a : Axis) : grad a (applyDiff ((S.val i m).curryLeft (basis a)) Green) x =
        c • (d • (x a • (Q a).field i m x) + R x • grad a ((Q a).field i m) x) := by
      have hb := (Q a).smooth i m x
      have hg (a : Axis) : grad a R x = d * x a := grad_power hx _ a
      rw [show grad a (applyDiff ((S.val i m).curryLeft (basis a)) Green) x =
        grad a (c • (R • (Q a).field i m)) x from GermD _ (he a),
        grad_smul (show ContDiffAt ℝ ∞ (R • (Q a).field i m) x from hr.smul hb), grad_times hr hb,hg,mul_smul d]
    simp_rw [ht, ← Finset.smul_sum, Finset.sum_add_distrib, ← Finset.smul_sum]
    have hq : ∑ a : Axis, grad a ((Q a).field i m) x = 0 := S.freeze_trace i m x
    rw [hq,smul_zero,add_zero, freeze_diagonal S i m x,smul_smul, smul_smul]
    congr 1
    have hn : n ≠ 0 := by dsimp [n]; positivity
    change n⁻¹ * ((-2)^j * normal) * (-(2*n)*rr x^(j+2)) = _
    rw [pow_succ]; field_simp; ring
end YM.Extra.FD
