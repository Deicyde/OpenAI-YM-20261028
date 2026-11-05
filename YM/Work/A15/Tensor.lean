import YM.Org.Input

/-!
# Components and rotation of stresses (A15)

Use the same vector convention `Ortho.move` as in the hierarchy.  The action
used **for averaging** is the label action together with the two compensating
index actions.  Its fixed points satisfy the required `Tensorial` law on
labels. Conservation transforms by `Laws.vector` with this same convention.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A15

open Table
open scoped BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L}

/-- Take a component, as a linear map. -/
def component (i j : Axis) : S.Stress →ₗ[ℂ] S.Field 4 :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : Axis => S.Field 4) j).comp
    (LinearMap.proj (R := ℂ) (φ := fun _ : Axis => Axis → S.Field 4) i)

lemma component_apply (J : S.Stress) (i j : Axis) : component i j J = J i j := rfl

/-- Contract on two vectors, also linear in the stress. -/
def contractStress (u v : E4) : S.Stress →ₗ[ℂ] S.Field 4 :=
  ∑ a : Axis, ∑ b : Axis, (((u a * v b : ℝ) : ℂ)) • component a b

lemma contractStress_apply (u v : E4) (J : S.Stress) :
    contractStress u v J = ∑ a : Axis, ∑ b : Axis, (((u a * v b : ℝ) : ℂ)) • J a b := by
  simp only [contractStress, LinearMap.sum_apply, LinearMap.smul_apply, component_apply]

lemma contractStress_basis (i j : Axis) (J : S.Stress) :
    contractStress (basis i) (basis j) J = J i j := by
  rw [contractStress_apply, Finset.sum_eq_single i]
  · simp
  · intro a _ ha; simp [ha]
  · simp

/-- Rotation with compensating index action. -/
def rotateStress (X : Rotation S) (K : Ortho) : S.Stress →ₗ[ℂ] S.Stress :=
  LinearMap.pi fun a => LinearMap.pi fun b =>
    ∑ i : Axis, ∑ j : Axis, (((K.val a i * K.val b j : ℝ) : ℂ)) •
      (X.act 4 K).toLinearMap.comp (component i j)

lemma rotateStress_apply (X : Rotation S) (K : Ortho) (J : S.Stress) (a b : Axis) :
    rotateStress X K J a b = ∑ i : Axis, ∑ j : Axis, (((K.val a i * K.val b j : ℝ) : ℂ)) •
      X.act 4 K (J i j) := by
  simp only [rotateStress, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, component_apply, LinearEquiv.coe_coe]

lemma move_inv_apply (K : Ortho) (x : E4) (i : Axis) :
    Ortho.move K⁻¹ x i = ∑ j, K.val j i * x j := by
  change M4.move (star K.val) x i = _
  simp only [M4.at_coord, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_apply]

private lemma swap_pairs {E : Type*} [AddCommMonoid E] (f : Axis → Axis → Axis → Axis → E) :
    ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
  have h :
      ∑ p : Axis × Axis, ∑ q : Axis × Axis, f p.1 p.2 q.1 q.2 =
      ∑ q : Axis × Axis, ∑ p : Axis × Axis, f p.1 p.2 q.1 q.2 := Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using h

private lemma sum_product (f g : Axis → ℝ) :
    (∑ a, f a) * (∑ b, g b) = ∑ a, ∑ b, f a * g b := by
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- Rotating the components pulls back the two vector arguments. -/
theorem contract_rotate (X : Rotation S) (K : Ortho) (J : S.Stress) (u v : E4) :
    contractStress u v (rotateStress X K J) = X.act 4 K
      (contractStress (Ortho.move K⁻¹ u) (Ortho.move K⁻¹ v) J) := by
  simp only [contractStress_apply, rotateStress_apply, move_inv_apply, sum_product,
    Complex.ofReal_sum, Finset.sum_smul, Finset.smul_sum, smul_smul,
    map_sum, map_smul]
  rw [swap_pairs]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.ofReal_mul]
  congr 2
  ring

theorem rotate_mul {V : DiffPlan S} {H : S.RealSpin} {X : Rotation S}
    (h : X.Laws V H) (K P : Ortho) (J : S.Stress) :
    rotateStress X K (rotateStress X P J) = rotateStress X (K * P) J := by
  funext i j
  rw [← contractStress_basis i j (rotateStress X K (rotateStress X P J)),
    ← contractStress_basis i j (rotateStress X (K * P) J)]
  simp only [contract_rotate, h.group, mul_inv_rev, Ortho.move_mul]

theorem tensorial_of_fixed (X : Rotation S) (J : S.Stress)
    (h : ∀ K, rotateStress X K J = J) : Tensorial X J := by
  intro K i j
  have e := contract_rotate X K J (Ortho.move K (basis i)) (Ortho.move K (basis j))
  rw [h, Ortho.inv_move, Ortho.inv_move, contractStress_basis] at e
  simpa only [contractStress_apply, Ortho.move, M4.move_basis] using e.symm

/-- Divergence, linear in the stress. -/
def divergenceMap (V : DiffPlan S) (b : Axis) : S.Stress →ₗ[ℂ] S.Field (4+1) :=
  ∑ a, (V.deriv 4 a).comp (component a b)

lemma divergenceMap_apply (V : DiffPlan S) (b : Axis) (J : S.Stress) :
    divergenceMap V b J = ∑ a : Axis, V.deriv 4 a (J a b) := by
  simp only [divergenceMap, LinearMap.sum_apply, LinearMap.comp_apply, component_apply]

private lemma reorder {E : Type*} [AddCommMonoid E] (f : Axis → Axis → Axis → E) :
    ∑ a, ∑ i, ∑ j, f a i j = ∑ j, ∑ i, ∑ a, f a i j := by
  rw [Finset.sum_comm] -- i a j
  calc
    ∑ i, ∑ a, ∑ j, f a i j = ∑ i, ∑ j, ∑ a, f a i j :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma rotate_divergence {V : DiffPlan S} {H : S.RealSpin} {X : Rotation S}
    (h : X.Laws V H) (K : Ortho) (J : S.Stress) (b : Axis) :
    divergenceMap V b (rotateStress X K J) = ∑ j : Axis,
      ((K.val b j : ℝ) : ℂ) • X.act (4+1) K (divergenceMap V j J) := by
  simp only [divergenceMap_apply, rotateStress_apply, map_sum, map_smul, h.vector,
    Finset.smul_sum, smul_smul]
  rw [reorder]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_mul, mul_comm (((K.val a i) : ℝ) : ℂ)]

theorem rotate_conserved {V : DiffPlan S} {H : S.RealSpin} {X : Rotation S}
    (h : X.Laws V H) (K : Ortho) (J : S.Stress) (c : Conserved V H J) :
    Conserved V H (rotateStress X K J) where
  symmetric a b := by
    rw [rotateStress_apply, rotateStress_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (K.val a i), c.symmetric i j]
  real a b := by
    simp only [rotateStress_apply, map_sum, map_smulₛₗ, h.real, c.real]
    simp
  divergence b := by
    rw [← divergenceMap_apply, rotate_divergence h]
    simp only [divergenceMap_apply, c.divergence, map_zero, smul_zero, Finset.sum_const_zero]

lemma conserved_real_smul {V : DiffPlan S} {H : S.RealSpin}
    (J : S.Stress) (h : Conserved V H J) (c : ℝ) : Conserved V H ((c : ℂ) • J) where
  symmetric a b := by simp only [Pi.smul_apply, h.symmetric a b]
  real a b := by
    simp only [Pi.smul_apply, map_smulₛₗ, h.real]
    simp
  divergence b := by
    rw [← divergenceMap_apply, map_smul, divergenceMap_apply, h.divergence, smul_zero]

end YM.Work.A15
