import YM.AnalyticBridge.VERIFIED_RESET_STEP.Clover

/-! Nonperiodic affine tests on local supports of literal based walks.
Clover at the anchor responds by exactly the constant curl. Recover
quadratic equality from limits of rays in the unmasked coefficient germs. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG StressFlux UVNext.PricedKernels Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint} {X : Support n}

abbrev line (v : Dir G n) (t : ℝ) := increment 1 (t • v)
@[simp] lemma line_zero (v : Dir G n) : line v 0 = 1 := by simp [line,at_zero]

namespace Square
lemma word_deriv (x : Site n) (l : Walk) (v : Dir G n) :
    HasDerivAt (fun t : ℝ => G.mat (travel (line v t) x l)) (G.colorMat (Exterior.linkSum v x l)) 0 := by
  let A : Exterior.fieldDir G n 1 := fun i => v (i.1,Exterior.axisEquiv.symm i.2)
  convert Exterior.curvature_linear G A x l using 1 <;>
    rw [show Exterior.collect G A = v from funext fun e => congr_arg (fun j => v (e.1,j)) (Exterior.axisEquiv.left_inv e.2)]

private lemma cochain_oriented (a b : Step) (v : Dir G n) (x : Site n) :
    Exterior.linkSum v x (oriented a b) = (flag a * flag b) • Exterior.linkSum v (atFace x a b) (square a.dir b.dir) := by
  rcases a with ⟨a,_|_⟩ <;> rcases b with ⟨b,_|_⟩ <;>
    simp [oriented,square, atFace, flag, posDir, negDir, Step.rev, Step.vec, Step.used, Exterior.linkSum, add_right_comm x, sub_eq_add_neg] <;> abel_nf
lemma cochain_square (i j : Axis) (v : Dir G n) (x : Site n) : Exterior.linkSum v x (square i j) =
    (v (x+step i,j)-v (x,j))-(v (x+step j,i)-v (x,i)) := by
  simp [square, Exterior.linkSum, Step.used, Step.vec, posDir,negDir]; abel_nf

lemma word_sum {o x : Site n} (a b : Step) (v : LinearJet G) (hx : 10*separation (atFace x a b) o < n.val) (hn : 4 ≤ n.val) :
    Exterior.linkSum (v.field o) x (oriented a b) = (flag a * flag b) • v.curl a.dir b.dir := by
  rw [cochain_oriented, cochain_square, v.field_step hx hn, v.field_step hx hn]; simp [LinearJet.curl]
lemma plate_deriv (a b : Step) (x o : Site n) (v : LinearJet G) (hx : 10*separation (atFace x a b) o < n.val) (hn : 4 ≤ n.val) :
    HasDerivAt (fun t : ℝ => plate (line (v.field o) t) x a b) ((flag a * flag b) • v.curl a.dir b.dir) 0 := by
  rw [← word_sum a b v hx hn]
  exact Work.F03.curvature_of_hasDerivAt (word_deriv x _ _)
end Square

lemma petals_deriv (a : PlaqAxes) (o : Site n) (hn : 20 < n.val) (v : LinearJet G) :
    HasDerivAt (fun t : ℝ => petals (line (v.field o) t) o a) (v.positive a) 0 := by
  have h i j := Square.plate_deriv i j o o v (by have := Square.near_face o i j; omega) (by omega)
  simp_rw [petals,clover,stencil]; refine HasDerivAt.congr_deriv (((h (posDir _) (posDir _)).sub (h _ (negDir _))).sub ((h (negDir _) _).sub (h _ _)) |>.const_smul (4:ℝ)⁻¹) ?_
  dsimp only [flag,posDir,negDir]; simp only [↓reduceIte,one_mul,mul_one,one_smul,neg_mul_neg,neg_one_smul,Bool.false_eq_true]; unfold LinearJet.positive; module

lemma hessian_limit {f : Pot G n} (hG : G.Simple) (hf : p.Regular X f) (h0 : f 1 = 0) (v : Dir G n) :
    Tendsto (fun t : ℝ => f (line v t) / t^2) (𝓝[≠] 0) (𝓝 (logHessian f v v / 2)) := by
  let F := germ f
  have he := germ_diff hf; have h := flat_critical hG hf
  rw [(show logHessian f v v = _ from (Work.F03.line_second he h v).symm)]
  exact Work.F03.taylor_limit_two ((show ContDiffAt ℝ 2 F ((0:ℝ) • v) by simpa using he).comp (0:ℝ) (f:=fun t => t • v) (by fun_prop))
    (show F ((0:ℝ) • v) = 0 by simp [F,germ,at_zero,h0]) (by
      have hh := (Push.side F (he.differentiableAt (by decide)) v).deriv
      simp only [F,h,zero_apply] at hh; exact hh)
lemma normalized_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {c : E} (hf : f 0 = 0) (h : HasDerivAt f c 0) :
    Tendsto (fun t : ℝ => t⁻¹ • f t) (𝓝[≠] 0) (𝓝 c) := by simpa [hf] using (hasDerivAt_iff_tendsto_slope_zero.mp h)
lemma pair_limit {f g : ℝ → G.Color} {a b : G.Color} (hf' : Tendsto (fun t : ℝ => t⁻¹ • f t) (𝓝[≠] 0) (𝓝 a))
    (hg' : Tendsto (fun t : ℝ => t⁻¹ • g t) (𝓝[≠] 0) (𝓝 b)) :
    Tendsto (fun t : ℝ => inner ℝ (f t) (g t) / t ^ 2) (𝓝[≠] 0) (𝓝 (inner ℝ a b)) := by
  refine (hf'.inner (𝕜:=ℝ) hg').congr fun t => ?_
  simp only [real_inner_smul_left,real_inner_smul_right,sq]; ring
lemma quad_limit {f : ℝ → Flux G} {a : Flux G} (h : ∀ i, Tendsto (fun t : ℝ => t⁻¹ • f t i) (𝓝[≠] 0) (𝓝 (a i))) (q : PlaqAxes → PlaqAxes → ℝ) :
    Tendsto (fun t : ℝ => quad q (f t) (f t) / t^2) (𝓝[≠] 0) (𝓝 (quad q a a)) := by
  simp_rw [quad,Finset.sum_div,mul_div_assoc]; exact tendsto_finsetSum _ fun _ _ => tendsto_finsetSum _ fun _ _ => (pair_limit (h _) (h _)).const_mul _
lemma petals_limit (a : PlaqAxes) (o : Site n) (hn : 20 < n.val) (v : LinearJet G) : Tendsto
      (fun t : ℝ => t⁻¹ • petals (line (v.field o) t) o a) (𝓝[≠] 0) (𝓝 (v.positive a)) := normalized_limit (by simp) (petals_deriv a o hn v)
lemma counter_limit (o : Site n) (hn : 20 < n.val) (v : LinearJet G) (q : PlaqAxes → PlaqAxes → ℝ) :
    Tendsto (fun t : ℝ => counter q o (line (v.field o) t) / t^2) (𝓝[≠] 0) (𝓝 (quad q v.positive v.positive / 2)) := by
  exact ((quad_limit (f:=fun t => petals (line (v.field o) t) o) (fun i => petals_limit i o hn v) q).div_const 2).congr fun t => by unfold counter; ring
lemma counter_diag (hG : G.Simple) (p : BudgetPoint) (o : Site n) (hn : 20 < n.val) (v : LinearJet G) (q : PlaqAxes → PlaqAxes → ℝ) :
    logHessian (counter q o) (v.field o) (v.field o) = quad q v.positive v.positive := by
  have h := tendsto_nhds_unique (hessian_limit hG (counter_regular o q p) (by simp [counter,quad]) (v.field o))
    (counter_limit o hn v q); linarith only [h]

lemma zero_by_diag {f : Pot G n} (hf : p.Regular X f) {a b : Dir G n} (h₁ : logHessian f a a = 0) (h₂ : logHessian f b b = 0)
    (h₃ : logHessian f (a+b) (a+b) = 0) : logHessian f a b = 0 := by
  simp only [hessian_eq,map_add,add_apply] at h₃; rw [← hessian_eq,h₁,← hessian_eq,← hessian_eq,← hessian_eq,h₂] at h₃
  linarith only [h₃, hessian_symm hf a b]
lemma affine_zero {f : Pot G n} (hf : p.Regular X f) (o : Site n) (h : ∀ v : LinearJet G, logHessian f (v.field o) (v.field o) = 0) :
    ∀ x y, IsAffineDirection o x → IsAffineDirection o y → logHessian f x y = 0 := by
  intro x y hx hy; obtain ⟨a,rfl⟩ := (LinearJet.isAffine o).mp hx; obtain ⟨b,rfl⟩ := (LinearJet.isAffine o).mp hy
  refine zero_by_diag hf (h a) (h b) ?_
  let z : LinearJet G := ⟨fun i => a.at0 i+b.at0 i,fun i j => a.slope i j+b.slope i j⟩
  convert h z <;> ext1 e <;> simp [z,LinearJet.field,smul_add,Finset.sum_add_distrib,add_add_add_comm]
end YM.AnalyticBridge.VerifiedReset
