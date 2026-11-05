import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07

/-!
# Contract Taylor coefficients of the actual free `Green` with harmonic tensors
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Kelvin
open Analysis Tensor Maxwell Function Set Filter ContinuousMultilinearMap
open scoped Topology BigOperators ContDiff

abbrev smoothAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E4 → F) (x : E4) := ContDiffAt ℝ ∞ f x
abbrev allOrders (j : ℕ) : (j : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

section Calculus
variable {x : E4} {f g : E4 → ℝ}
lemma gsmooth (h : smoothAt f x) (i : Axis) : smoothAt (grad i f) x := grad_smooth _ h (by simp)
lemma gcomm (h : smoothAt f x) (i j : Axis) : grad i (grad j f) x = grad j (grad i f) x :=
  grad_comm (h.of_le (allOrders 2)) _ _
lemma prod_grad (h : smoothAt f x) (p : smoothAt g x) (i : Axis) :
    grad i (fun y => f y * g y) x = grad i f x * g x + f x * grad i g x := by
  simp only [grad,D,fderiv_fun_mul (h.differentiableAt (by simp)) (p.differentiableAt (by simp)),add_apply, smul_apply,smul_eq_mul]
  ring
lemma const_grad (h : smoothAt f x) (a : ℝ) (i) : grad i (fun y => a * f y) x = a * grad i f x := by
  rw [prod_grad (f := fun _ => a) contDiffAt_const h]; simp [grad,D]
lemma sum_grad {ι : Type*} [Fintype ι] (f : ι → E4 → ℝ) (h : ∀ i, smoothAt (f i) x) (a : Axis) :
    grad a (fun y => ∑ i, f i y) x = ∑ i, grad a (f i) x := by
  rw [grad,D,fderiv_fun_sum (fun i _ => (h i).differentiableAt (by simp)),sum_apply]
  rfl

def Harmonic (f : E4 → ℝ) (x : E4) := ∑ i : Axis, grad i (grad i f) x = 0

lemma harmonic_grad (h : smoothAt f x) (hh : ∀ᶠ y in 𝓝 x, Harmonic f y) (b : Axis) : Harmonic (grad b f) x := by
  have he (i : Axis) : grad i (grad b f) =ᶠ[𝓝 x] grad b (grad i f) := by
    filter_upwards [(h.of_le (allOrders 2)).eventually (by simp)] with y hy
    exact grad_comm hy ..
  have hw (i) : grad i (grad i (grad b f)) x = grad b (grad i (grad i f)) x :=
    (GermD _ (he i)).trans (gcomm (gsmooth h _) _ _)
  unfold Harmonic
  simp_rw [hw, ← sum_grad (fun i => grad i (grad i f)) (fun i => gsmooth (gsmooth h _) _) b]
  exact (GermD _ hh).trans (show grad b (fun _ : E4 => (0:ℝ)) x = 0 by simp [grad,D])

lemma harmonic_form {U : Set E4} (hU : IsOpen U) {f : Maxwell.Field ℝ} (h : WaveOn U f) (hx : x ∈ U) (a b : Axis) :
    Harmonic (f a b) x := by
  have hs i j k := gsmooth (h.smooth j k x hx) i
  have h' (i k) : grad a (f i k) =ᶠ[𝓝 x] -grad a (f k i) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have he : f i k =ᶠ[𝓝 y] - f k i := by
      filter_upwards [hU.mem_nhds hy] with z hz; exact h.form i k z hz
    exact (GermD _ he).trans (by simp [grad,D]; rw [fderiv_neg]; rfl)
  have he i : grad i (f a b) =ᶠ[𝓝 x] grad a (f i b) - grad b (f i a) := by
    filter_upwards [hU.mem_nhds hx, h' b i] with y hy he
    have hz := h.cycle i a b y hy
    change _ = -grad a (f i b) y at he
    rw [he] at hz; dsimp; linarith
  have hq (i) : grad i (grad i (f a b)) x = grad a (grad i (f i b)) x - grad b (grad i (f i a)) x := by
    change D (basis i) (grad i (f a b)) x = _; rw [GermD _ (he i)]
    exact (Bare.grad_sub (hs a i b) (hs b i a) i).trans (by rw [gcomm (h.smooth i b x hx) i a, gcomm (h.smooth i a x hx) i b])
  have hv (j k) : ∑ i, grad j (grad i (f i k)) x = 0 := by
    rw [← sum_grad _ (fun i => hs i i k)]
    have ht : (fun y => ∑ i, grad i (f i k) y) =ᶠ[𝓝 x] fun y => 0 := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact h.divergence k y hy
    exact (GermD _ ht).trans (by simp [D])
  simp [Harmonic,hq, Finset.sum_sub_distrib, hv]

/-- One inverse norm squared, before the `normal`. -/
def R (x : E4) := (‖x‖^2)⁻¹
lemma R_smooth (hx : x ≠ 0) : smoothAt R x :=
  (contDiff_norm_sq ℝ).contDiffAt.inv (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))
lemma R_deriv (hx : x ≠ 0) (i : Axis) : grad i R x = -2 * R x ^ 2 * x i := by
  have he := first_Green hx i
  rw [show Green = fun x => normal * R x from rfl, const_grad (R_smooth hx)] at he
  apply mul_left_cancel₀ (show normal ≠ 0 from normal_pos.ne')
  rw [he,R]; ring
lemma R_pow_grad (hx : x ≠ 0) (j : ℕ) (i : Axis) :
    grad i (fun y => R y ^ j) x = -2 * j * R x ^ (j+1) * x i := by
  induction j with
  | zero => simp [grad,D]
  | succ j ih => rw [show (fun y => R y ^ (j+1)) = _ from funext fun y => pow_succ (R y) j,
      prod_grad ((R_smooth hx).pow j) (R_smooth hx), R_deriv hx, ih]; push_cast; simp only [pow_succ]; ring
end Calculus

variable {j : ℕ}
lemma partial_diag (A : T E4 ℝ (j+1)) (hs : Sym A) (i : Axis) (x : E4) :
    grad i (diagonal A) x = (j+1 : ℝ) * diagonal (A.curryLeft (basis i)) x := by
  rw [grad,D,differential_diagonal A hs]; simp [Tensor.diagonal]

lemma harmonic_sum (A : T E4 ℝ (j+1)) (hs : Sym A) (x : E4) (hh : Harmonic (diagonal A) x) :
    ∑ i : Axis, grad i (diagonal (A.curryLeft (basis i))) x = 0 := by
  have he i := funext (partial_diag A hs i)
  unfold Harmonic at hh
  conv at hh => lhs; arg 2; intro i; rw [he i,const_grad (diag_smooth _ ∞ |>.contDiffAt)]
  rw [← Finset.mul_sum] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by positivity)

lemma harmonic_curry (A : T E4 ℝ (j+1)) (hs : Sym A) (hh : ∀ x, Harmonic (diagonal A) x) (i : Axis) (x : E4) :
    Harmonic (diagonal (A.curryLeft (basis i))) x := by
  have he := harmonic_grad (x := x) (diag_smooth A ∞ |>.contDiffAt) (Eventually.of_forall hh) i
  let f := diagonal (A.curryLeft (basis i))
  have hF y : smoothAt f y := (diag_smooth _ ∞).contDiffAt
  have hG (k : Axis) : grad k (grad i (diagonal A)) = fun x => (j+1 : ℝ) * grad k f x := by
    rw [funext (partial_diag A hs i)]
    exact funext fun y => const_grad (hF y) _ k
  simp only [Harmonic,hG,const_grad (gsmooth (hF x) _),← Finset.mul_sum] at he
  exact (mul_eq_zero.mp he).resolve_left (by positivity)

lemma space_expand (x : E4) : ∑ i : Axis, x i • basis i = x := by ext1 i; simp
lemma euler_step (A : T E4 ℝ (j+1)) (x : E4) : ∑ i : Axis, x i * diagonal (A.curryLeft (basis i)) x = diagonal A x := by
  rw [show diagonal A x = diagonal (A.curryLeft x) x by unfold Tensor.diagonal; rw [curryLeft_apply]; congr; exact Fin.cons_self_tail (fun _ => x) |>.symm]
  conv_rhs => lhs; arg 2; rw [← space_expand x]
  simp [Tensor.diagonal, map_smul, smul_eq_mul]

def diffOp (A : T E4 ℝ j) (f : E4 → ℝ) (x : E4) :=
  ∑ u : Fin j → Axis, A (basis ∘ u) * coeff f j x (basis ∘ u)

lemma smooth_diffOp (A : T E4 ℝ j) {x : E4} {f : E4 → ℝ} (h : smoothAt f x) : smoothAt (diffOp A f) x := by
  apply ContDiffAt.sum (f := fun i x => A (basis ∘ i) * coeff f j x (basis ∘ i)); intro i _
  exact contDiffAt_const.mul ((ContinuousMultilinearMap.apply ℝ (fun _ => E4) ℝ (basis ∘ i)).contDiff.contDiffAt.comp x (coeff_smooth h j))
lemma grad_diffOp (A : T E4 ℝ j) {x : E4} {f : E4 → ℝ} (h : smoothAt f x) (i : Axis) :
    grad i (diffOp A f) x = diffOp A (grad i f) x := by
  let K (u : Fin j → Axis) := ContinuousMultilinearMap.apply ℝ (fun _ => E4) ℝ (basis ∘ u)
  have hs u : smoothAt (fun y => coeff f j y (basis ∘ u)) x := (K u).contDiff.contDiffAt.comp x (coeff_smooth h j)
  unfold diffOp; rw [sum_grad _ (fun u => contDiffAt_const.mul (hs u))]
  simp_rw [const_grad (hs _)]
  apply Finset.sum_congr rfl; intro u _; congr 1
  rw [show (fun y => coeff f j y (basis ∘ u)) = K u ∘ coeff f j from rfl, grad_linear _ (coeff_smooth h j)]
  exact congr_arg (fun Q : T E4 ℝ j => Q (basis ∘ u)) (D_coeff (h.of_le (allOrders _)) _)

lemma diffOp_step (A : T E4 ℝ (j+1)) {f : E4 → ℝ} {x : E4} (h : smoothAt f x) :
    diffOp A f x = ((j : ℝ)+1)⁻¹ * ∑ i : Axis, grad i (diffOp (A.curryLeft (basis i)) f) x := by
  simp_rw [grad_diffOp _ h, diffOp,Finset.mul_sum]
  rw [← Fintype.sum_prod_type' (α₁ := Axis) (α₂ := Fin j → Axis)]
  symm
  let e := Fin.consEquiv (fun _ : Fin (j+1) => Axis)
  apply Fintype.sum_equiv e
  rintro ⟨i,u⟩
  have he : basis ∘ (e (i,u)) = Fin.cons (basis i) (basis ∘ u) := by ext1 a; exact Fin.cases rfl (fun _ => rfl) a
  dsimp only; rw [he, coeff_apply_cons (h.of_le (allOrders _)),curryLeft_apply]; simp [grad]; ring

/-- Homogeneous differentiation of the 4D Green kernel against a harmonic symmetric tensor. -/
theorem harmonic_Green (A : T E4 ℝ j) (hs : Sym A) (hh : ∀ x, Harmonic (diagonal A) x)
    {x : E4} (hx : x ≠ 0) : diffOp A Green x = ((-2)^j * normal) * (R x ^ (j+1) * diagonal A x) := by
  induction j generalizing x with
  | zero =>
    simp only [diffOp, Fintype.sum_unique, coeff_apply_zero, pow_zero,one_mul, Nat.zero_add, pow_one]
    rw [show ∀ z : Fin 0 → Axis, A (basis ∘ z) = diagonal A x from fun _ => congr_arg A (Subsingleton.elim ..)]
    unfold Green R Tensor.diagonal; ring
  | succ j ih =>
    let F (i : Axis) := A.curryLeft (basis i)
    let a := (-2)^j * normal
    have he i : diffOp (F i) Green =ᶠ[𝓝 x] fun y => a * ((R y)^(j+1) * diagonal (F i) y) := by
      filter_upwards [open_away.mem_nhds hx] with y hy
      exact ih (F i) (freeze_sym A hs _) (harmonic_curry A hs hh i) hy
    have hv (i) : grad i (diffOp (F i) Green) x =
        a * ((-2 * ((j+1 : ℕ) : ℝ) * R x ^ (j+2)) * (x i * diagonal (F i) x) + R x ^ (j+1) * grad i (diagonal (F i)) x) := by
      have hs := (R_smooth hx).pow (j+1)
      have hF := (diag_smooth (F i) ∞).contDiffAt (x := x)
      rw [show grad i (diffOp (F i) Green) x = grad i (fun y => a * ((R y)^(j+1) * diagonal (F i) y)) x from GermD _ (he i),
        const_grad (hs.mul hF), prod_grad hs hF, R_pow_grad hx (j+1) i]
      ring
    have hz : ∑ i, grad i (diagonal (F i)) x = 0 := harmonic_sum _ hs x (hh x)
    rw [diffOp_step A (freeSmooth hx)]
    simp_rw [show ∀ i, A.curryLeft (basis i) = F i from fun _ => rfl,hv,← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum,hz,show ∑ i : Axis, x i * diagonal (F i) x = diagonal A x from euler_step A x]
    rw [pow_succ (-2 : ℝ)]; push_cast; field_simp; ring
end YM.Push.FiniteDetection.Kelvin
