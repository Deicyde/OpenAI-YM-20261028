import YM.Gauge.Chart
import YM.RG.Masks


/-!
# Left Wilson derivative

Directions are **left increments on positive** edges (`RG.increment`). We reorient each
of the plaquettes contributing to a bond, taking the given bond first and positively. No inclusion of `β` in the gradient. The formulas also work on small tori where the
same edge may be read several times.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Lattice RG Wilson MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace

variable {G : Gauge}

/-- Left increment used even on the infinite cover (on finitely many input links
when we form an equation). -/
def left (a : G.Color) (u : G.El) (t : ℝ) := G.lieExp (t • a) * u

@[simp] lemma left_zero (a : G.Color) (u : G.El) : left a u 0 = u := by
  simp [left]

lemma left_add (a : G.Color) (u : G.El) (s t : ℝ) : left a (left a u t) s = left a u (s+t) := by
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  apply G.mat_injective; unfold left; simp only [Gauge.mat_mul, G.mat_lieExp, map_smul]
  rw [add_smul, ← mul_assoc]; congr 1
  exact (NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left _).smul_right _)).symm

lemma matLeft_at (a : G.Color) (u : G.El) (t : ℝ) :
    DifferentiableAt ℝ (fun s : ℝ => G.mat (left a u s)) t := by
  unfold left; simp only [G.mat_mul, G.mat_lieExp, map_smul]
  exact ((hasDerivAt_exp_smul_const (G.colorMat a) t).differentiableAt).mul_const _

lemma matLeft_zero (a : G.Color) (u : G.El) :
    HasDerivAt (fun t => G.mat (left a u t)) (G.colorMat a * G.mat u) 0 := by
  unfold left; simp only [G.mat_mul, G.mat_lieExp, map_smul]
  simpa using! (hasDerivAt_exp_smul_const (G.colorMat a) (0 : ℝ)).mul_const (G.mat u)

attribute [local instance] Gauge.frobInner in
lemma left_component (a : G.Color) (u : G.El) :
    inner ℝ a (G.curvature u) = - (G.colorMat a * G.mat u).trace.re / G.repDim := by
  let X := G.colorMat a
  let Y := G.mat u
  let Z := (1/2 : ℝ) • (Y-star Y)
  have he (A : G.Mat) : (star A).trace.re = A.trace.re := by
    rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]; rfl
  have h : (X * star Y).trace.re = - (X * Y).trace.re := by
    rw [← he (X*star Y), star_mul, star_star, show star X = -X from G.colorMat_skew a,
      mul_neg, Matrix.trace_neg, Matrix.trace_mul_comm, Complex.neg_re]
  have hX : X ∈ G.lie := G.colorMat_mem a
  have ht : inner ℝ X Z = - (X * Y).trace.re := by
    change (X * star Z).trace.re = _; dsimp only [Z]
    simp only [star_smul,star_trivial,star_sub,star_star,mul_smul_comm,mul_sub,
      Matrix.trace_sub,Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero,
      Complex.sub_re,h]
    ring
  have hQ : inner ℝ X Z = inner ℝ X (G.lie.starProjection Z) := by
    apply sub_eq_zero.mp
    rw [← inner_sub_right, real_inner_comm]; exact Submodule.starProjection_inner_eq_zero _ _ hX
  have hu : G.colorMat (G.curvature u) = G.lie.starProjection Z := G.colorMat_project _
  have HZ : inner ℝ X Z = (G.repDim : ℝ) * inner ℝ a (G.curvature u) := by
    rw [hQ, ← hu]; exact G.inner_frob_color a (G.curvature u)
  rw [eq_div_iff (by positivity), mul_comm]; exact HZ.symm.trans ht

lemma price_left (a : G.Color) (u : G.El) :
    HasDerivAt (fun t => G.price (left a u t)) (inner ℝ a (G.curvature u)) 0 := by
  let L := Complex.reCLM.comp (Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap
  have h := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ((L.hasFDerivAt.comp_hasDerivAt 0
    (matLeft_zero a u)).div_const (G.repDim:ℝ)))
  apply h.congr_deriv
  change 0 - _ / (G.repDim:ℝ) = _
  rw [zero_sub,left_component,neg_div]; rfl

private lemma price_roll (u v : G.El) : G.price (u*v) = G.price (v*u) := by
  have h := G.price_conj v (u*v); simp only [mul_assoc, mul_inv_cancel, mul_one] at h; exact h.symm

/-- Four occurrences, counting reversed links by taking the inverse of the
loop. Keep occurrences separate before putting them on the lattice. -/
theorem quad_cost (a b c d : G.Color) (u v w z : G.El) :
    HasDerivAt (fun t => G.price (left a u t * left b v t * (left c w t)⁻¹ * (left d z t)⁻¹))
      (inner ℝ a (G.curvature (u*v*w⁻¹*z⁻¹)) +
       inner ℝ b (G.curvature (v*w⁻¹*z⁻¹*u)) +
       inner ℝ c (G.curvature (w*v⁻¹*u⁻¹*z)) +
       inner ℝ d (G.curvature (z*w*v⁻¹*u⁻¹))) 0 := by
  let F := fun x : Axis → ℝ => G.price (left a u (x 0) * left b v (x 1) *
    (left c w (x 2))⁻¹ * (left d z (x 3))⁻¹)
  have hf : DifferentiableAt ℝ F 0 := by
    let A := fun x : Axis → ℝ => G.mat (left a u (x 0)) * G.mat (left b v (x 1)) *
      star (G.mat (left c w (x 2))) * star (G.mat (left d z (x 3)))
    have he (p : G.Color) (q : G.El) (i : Axis) : DifferentiableAt ℝ
        (fun x : Axis → ℝ => G.mat (left p q (x i))) 0 :=
      (matLeft_at p q _).comp _ (ContinuousLinearMap.proj (φ:=fun _ : Axis => ℝ) i).differentiableAt
    have hh := (((he a u 0).mul (he b v 1)).mul (he c w 2).star).mul (he d z 3).star
    let R := Complex.reCLM.comp (Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap
    change DifferentiableAt ℝ (fun x => (1:ℝ) - R (A x) / G.repDim) 0
    simp_rw [div_eq_mul_inv]
    exact DifferentiableAt.sub (show DifferentiableAt ℝ (fun x : (Axis → ℝ) => (1 : ℝ)) 0 from differentiableAt_const _)
      ((R.differentiableAt.comp _ (show DifferentiableAt ℝ A 0 from hh)).mul_const _)
  let L := fderiv ℝ F 0
  have he (x : Axis → ℝ) : HasDerivAt (fun t : ℝ => F (t • x)) (L x) 0 :=
    hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 (show HasDerivAt (fun t : ℝ => t • x) x 0 by
      simpa using! (hasDerivAt_id' (0:ℝ)).smul_const x) (by simp)
  let s (i : Axis) : Axis → ℝ := Pi.single i 1
  have h₀ : L (s 0) = inner ℝ a (G.curvature (u*v*w⁻¹*z⁻¹)) := by
    apply (he (s 0)).unique
    rw [show (fun t : ℝ => F (t • s 0)) = (fun t => G.price (left a (u*v*w⁻¹*z⁻¹) t)) by
      funext t; dsimp only [F]
      simp [s]; simp only [left,mul_assoc]]
    exact price_left _ _
  have h₁ : L (s 1) = inner ℝ b (G.curvature (v*w⁻¹*z⁻¹*u)) := by
    apply (he (s 1)).unique
    rw [show (fun t : ℝ => F (t • s 1)) = (fun t => G.price (left b (v*w⁻¹*z⁻¹*u) t)) by
      funext t; dsimp only [F]; simp [s, mul_assoc]; rw [price_roll]; simp only [left,mul_assoc]]
    exact price_left _ _
  have h₂ : L (s 2) = inner ℝ c (G.curvature (w*v⁻¹*u⁻¹*z)) := by
    apply (he (s 2)).unique
    rw [show (fun t : ℝ => F (t • s 2)) = (fun t => G.price (left c (w*v⁻¹*u⁻¹*z) t)) by
      funext t; dsimp only [F]; simp [s]; rw [← G.price_inv (u * v * _ * z⁻¹)]
      simp only [mul_inv_rev, inv_inv]; rw [price_roll]; simp only [left,mul_assoc]]
    exact price_left _ _
  have h₃ : L (s 3) = inner ℝ d (G.curvature (z*w*v⁻¹*u⁻¹)) := by
    apply (he (s 3)).unique
    rw [show (fun t : ℝ => F (t • s 3)) = (fun t => G.price (left d (z*w*v⁻¹*u⁻¹) t)) by
      funext t; dsimp only [F]; simp [s]; rw [← G.price_inv (u * v * _ * _)]
      simp only [mul_inv_rev, inv_inv,left,mul_assoc]]
    exact price_left _ _
  have hh : (1 : Axis → ℝ) = s 0 + s 1 + s 2 + s 3 := by
    ext x; fin_cases x <;> simp [s, Axis]
  have hz := he (1 : Axis → ℝ)
  conv at hz => arg 2; rw [hh, map_add,map_add,map_add,h₀,h₁,h₂,h₃]
  simpa [F] using hz

section Lattice
variable {R : Type*} [AddCommGroup R] [One R]

/-- One of the surrounding plaquettes in positive-link convention (with a signed
transverse axis as parameter). This is the value at the base of the edge. -/
def wheel (e : Edge (Four R)) (d : Step) (U : Links R G.El) :=
  travel U e.1 (oriented (posDir e.2) d)

theorem wheel_pos (U : Links R G.El) (x : Four R) (i j : Axis) :
    wheel (x,i) (posDir j) U = U (x,i)*U (x+step i,j)*(U (x+step j,i))⁻¹*(U (x,j))⁻¹ := by
  have h : x + Lattice.step i + step j + -(step i) = x + step j := by abel
  unfold wheel oriented
  simp only [travel, Step.pos_read, Step.vec_pos, Step.vec_neg, Step.rev_pos, Step.neg_read,
    h, add_sub_cancel_right, mul_one, mul_assoc]
  rw [sub_eq_add_neg, h]

theorem wheel_neg (U : Links R G.El) (x : Four R) (i j : Axis) :
    wheel (x,i) (negDir j) U = U (x,i)*(U (x - step j+step i,j))⁻¹*(U (x-step j,i))⁻¹*U (x-step j,j) := by
  have h : x + step i + -(step j) = x-step j + step i := by abel
  unfold wheel oriented
  simp only [travel, Step.pos_read, Step.vec_pos, Step.vec_neg, Step.rev_pos, Step.neg_read,
    Step.rev_neg,h, add_sub_cancel_right, mul_one, mul_assoc, add_neg_cancel_right]
  rw [sub_eq_add_neg (x + step i), h]

/-- The Euler gradient with respect to positive links. -/
def euler (U : Links R G.El) (e : Edge (Four R)) : G.Color :=
  ∑ j : Axis with j ≠ e.2, (G.curvature (wheel e (posDir j) U) + G.curvature (wheel e (negDir j) U))

@[fun_prop] lemma continuous_euler {e : Edge (Four R)} : Continuous fun U : Links R G.El => euler U e := by
  unfold euler wheel; fun_prop

lemma euler_gauge (U : Links R G.El) (e : Edge (Four R)) (T : Four R → G.El) :
    euler (Lattice.gauge T U) e = G.adjoint (T e.1) (euler U e) := by
  simp only [euler,wheel,travel_gauge,stop_oriented,G.curvature_conjugate,map_add,map_sum]
end Lattice

lemma euler_at {n : Side} (U : Config G n) (o : Site n) (x : Cover) (i : Axis) :
    euler (expandAt o U) (x,i) = euler U (wrap n x + o,i) := by simp only [euler,wheel, travel_at]

private lemma plaquette_tall (f : Axis → Axis → ℝ) :
    (∑ x : PlaqAxes, (f x.val.1 x.val.2 + f x.val.2 x.val.1)) =
      ∑ i : Axis, ∑ j : Axis with j ≠ i, f i j := by
  let u := (Finset.univ.filter fun x : Axis × Axis => x.1 < x.2)
  have he (g : Axis → Axis → ℝ) : ∑ x : PlaqAxes, g x.val.1 x.val.2 =
      ∑ i : Axis, ∑ j : Axis, if i < j then g i j else 0 := by
    rw [← (Finset.sum_subtype (p:=fun x : Axis × Axis => x.1 < x.2) u
      (fun x => by unfold u; simp) (fun x => g x.1 x.2)), Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_add_distrib, he f, he (fun j i => f i j),
    Finset.sum_comm (f:=fun i j => if i<j then f j i else 0), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib,Finset.sum_filter]
  apply Finset.sum_congr rfl; intro j _
  by_cases hj : j < i
  · simp only [if_pos hj, if_neg hj.asymm, if_pos hj.ne, zero_add]
  by_cases ht : i < j
  · simp only [if_pos ht, if_neg ht.asymm, if_pos ht.ne',add_zero]
  have h : i=j := le_antisymm (le_of_not_gt hj) (le_of_not_gt ht)
  simp only [h,lt_irrefl, ne_eq, not_true_eq_false, ↓reduceIte, add_zero]

variable {n : Side}

/-- Differentiating with independent left increments. The sum on the left
(inside `energy`) is unordered axis pairs, on the right each link gets both
incidences with each transverse axis. -/
theorem derivative_energy (U : Config G n) (A : Directions G n) :
    HasDerivAt (fun t : ℝ => energy (increment U (t • A)))
      (∑ e : Edge (Site n), inner ℝ (A e) (euler U e)) 0 := by
  let f (x : Site n) (i : Axis) (d : Step) := inner ℝ (A (x,i)) (G.curvature (wheel (x,i) d U))
  let g (x : Site n) (i j : Axis) := f x i (posDir j) + f (x+step i) j (negDir i) +
    f (x+step j) i (negDir j) + f x j (posDir i)
  have he (p : Face (Per n)) : HasDerivAt (fun t : ℝ => G.price (faceValue (increment U (t • A)) p))
      (g p.1 p.2.val.1 p.2.val.2) 0 := by
    rcases p with ⟨x,⟨⟨i,j⟩,hij⟩⟩
    have H : ∀ V : Config G n, faceValue V (x,⟨(i,j),hij⟩) = wheel (x,i) (posDir j) V := fun _ => rfl
    simp_rw [H]
    dsimp only [g,f]
    rw [wheel_neg,wheel_neg,wheel_pos,wheel_pos]
    simp_rw [wheel_pos, add_sub_cancel_right]
    exact quad_cost ..
  have hi := HasDerivAt.fun_sum (u:=Finset.univ) fun p _ => he p
  apply hi.congr_deriv
  let W i j := ∑ x : Site n, (f x i (posDir j) + f x i (negDir j))
  have hh (i : Axis) (d : Step) (b : Site n) : ∑ x : Site n, f (x+b) i d = ∑ x : Site n, f x i d :=
    Equiv.sum_comp (Equiv.addRight b) fun x => f x i d
  have ht (i j : Axis) : ∑ x : Site n, g x i j = W i j + W j i := by
    simp only [g,W,Finset.sum_add_distrib]; rw [hh j, hh i]; abel
  rw [Fintype.sum_prod_type (fun p : Face (Per n) => _), Finset.sum_comm]
  simp_rw [ht]
  rw [plaquette_tall, Fintype.sum_prod_type (fun e : Edge (Site n) => _), Finset.sum_comm (f:=fun x i => inner ℝ (A (x,i)) (euler U (x,i)))]
  apply Finset.sum_congr rfl; intro i _
  rw [show ∑ j : Axis with j≠i, W i j = _ from Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  simp_rw [euler,inner_sum,inner_add_right]; rfl

end YM.WardBin
