import YM.Gauge.MatrixGroup
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Lie algebra of the actual gauge image

One-parameter definition (`exp` for matrices); we verify closure rather than
postulating a tangent calculus. Use the Frobenius norm. Applies also to disconnected G.
The exponential chart & Haar Jacobian still need their own work.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Gauge

open Filter Set Topology NormedSpace
open scoped Matrix.Norms.Frobenius

variable (G : Gauge)

/-- One-parameter generators of this closed subgroup, in the defining representation. -/
def Generates (X : G.Mat) : Prop := ∀ t : ℝ, exp (t • X) ∈ range G.mat

section Curve
variable {f : ℝ → G.Mat} {X : G.Mat}

theorem tangent_skew (h : HasDerivAt f X 0) (h0 : f 0 = 1)
    (hm : ∀ t, f t ∈ range G.mat) : star X = - X := by
  have hg : f * (fun t => star (f t)) = fun _ => 1 := by
    funext t
    obtain ⟨u, hu⟩ := hm t
    simpa only [Pi.mul_apply, ← hu] using G.mat_mul_star u
  have h' := h.mul h.star
  rw [hg, h0] at h'
  have e := h'.unique (hasDerivAt_const _ _)
  simpa [eq_neg_iff_add_eq_zero, add_comm X] using e

theorem generates_skew (h : G.Generates X) : star X = -X := by
  apply G.tangent_skew (f := fun t : ℝ => exp (t • X)) _ (by simp) h
  simpa using! (hasDerivAt_exp_smul_const X (0 : ℝ))

/-- Frobenius norm avoids exponential constants in telescoping. -/
theorem frob_pow_difference (A B : G.Mat) (ha : A ∈ GaugeU G.n) (hb : B ∈ GaugeU G.n)
    (k : ℕ) : ‖A^k - B^k‖ ≤ k * ‖A - B‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ = ‖A^k*(A-B) + (A^k-B^k)*B‖ := by simp only [pow_succ, mul_sub, sub_mul]; congr 1; abel
      _ ≤ ‖A^k*(A-B)‖ + ‖(A^k-B^k)*B‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [frob_mul_eq _ _ (Matrix.mem_unitaryGroup_iff.mp hb),
          mul_frob_eq _ _ (Matrix.mem_unitaryGroup_iff'.mp ((GaugeU G.n).pow_mem ha k)),
          Nat.cast_add_one, add_mul, one_mul, add_comm ‖A-B‖]
        gcongr

theorem tangent_approx (h : HasDerivAt f X 0) (h0 : f 0 = 1)
    (hm : ∀ t, f t ∈ range G.mat) :
    Tendsto (fun n : ℕ => (f (n : ℝ)⁻¹) ^ n) atTop (𝓝 (exp X)) := by
  let F (t : ℝ) : G.Mat := exp (t • X)
  have he : HasDerivAt F X 0 := by
    simpa [F] using! hasDerivAt_exp_smul_const X (0 : ℝ)
  have hk : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    simpa using (ne_of_gt hn)
  have e : F 0 = 1 := by simp [F]
  have hd : Tendsto (fun n : ℕ => (n : ℝ) * ‖f (n : ℝ)⁻¹ - F (n : ℝ)⁻¹‖)
      atTop (𝓝 0) := by
    have := (((h.sub he).tendsto_slope).norm).comp hk
    simpa only [Function.comp_def, slope_def_module, sub_zero, inv_inv,
      Pi.sub_apply, e, h0, sub_self, sub_zero, norm_smul, Real.norm_natCast,
      norm_zero] using this
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) _ hd
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hX := G.tangent_skew h h0 hm
  have hpow : F (n : ℝ)⁻¹ ^ n = exp X := by
    haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
    dsimp only [F]
    have e0 : exp (n • ((n : ℝ)⁻¹ • X)) = exp ((n : ℝ)⁻¹ • X) ^ n := exp_nsmul n _
    rw [← e0, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀, one_smul]
    exact ne_of_gt (by exact_mod_cast hn)
  rw [← hpow]
  apply G.frob_pow_difference
  · obtain ⟨u, hu⟩ := hm ((n : ℝ)⁻¹)
    rw [← hu]; exact u.val.property
  · haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
    apply exp_mem_unitary_of_mem_skewAdjoint
    change star ((n : ℝ)⁻¹ • X) = -((n : ℝ)⁻¹ • X)
    rw [star_smul, hX, star_trivial, smul_neg]

theorem tangent_generates (h : HasDerivAt f X 0) (h0 : f 0 = 1)
    (hm : ∀ t, f t ∈ range G.mat) : G.Generates X := by
  intro t
  let F := fun s : ℝ => f (t*s)
  have dh : HasDerivAt F (t • X) 0 := by
    simpa [F, Function.comp_def] using! h.scomp_of_eq _ ((hasDerivAt_id' (0 : ℝ)).const_mul t) (by simp)
  apply G.closed_matrices.mem_of_tendsto (G.tangent_approx dh (by simp [F, h0])
    fun s ↦ hm (t*s))
  refine Eventually.of_forall fun n ↦ ?_
  obtain ⟨u, hu⟩ := hm (t*(n : ℝ)⁻¹)
  refine ⟨u^n, ?_⟩
  let b : G.El →* G.Mat := { toFun := G.mat, map_one' := rfl, map_mul' := G.mat_mul }
  change b (u ^ n) = f _ ^ n
  simp only [map_pow, b, MonoidHom.coe_mk, OneHom.coe_mk, hu]
end Curve

theorem generates_add {X Y : G.Mat} (hx : G.Generates X) (hy : G.Generates Y) :
    G.Generates (X+Y) := by
  let f := fun t : ℝ => exp (t • X)
  let g := fun t : ℝ => exp (t • Y)
  apply G.tangent_generates (f := f * g) _ (by simp [f, g])
  · intro t
    obtain ⟨u, hu⟩ := hx t
    obtain ⟨v, hv⟩ := hy t
    exact ⟨u*v, by simp [hu, hv, f, g]⟩
  simpa [f, g] using!
    (hasDerivAt_exp_smul_const X (0 : ℝ)).mul (hasDerivAt_exp_smul_const Y (0 : ℝ))

def lie : Submodule ℝ G.Mat where
  carrier := G.Generates
  add_mem' := G.generates_add
  zero_mem' := by
    intro t
    exact ⟨(1:G.El), by simp⟩
  smul_mem' s _ h t := by

    rw [smul_smul]
    exact h (t*s)

abbrev Alg := ↥G.lie

@[simp] theorem mem_lie {X : G.Mat} : X ∈ G.lie ↔ G.Generates X := Iff.rfl

theorem closed_lie : IsClosed (G.lie : Set G.Mat) := G.lie.closed_of_finiteDimensional

/-- Conjugation in the defining representation. -/
def conjugate (u : G.El) (X : G.Mat) := G.mat u * X * star (G.mat u)

theorem exp_conjugate (u : G.El) (X : G.Mat) : exp (G.conjugate u X) = G.conjugate u (exp X) := by
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  let w : G.Matˣ := ⟨G.mat u, star (G.mat u), G.mat_mul_star u, G.mat_star_mul u⟩
  exact exp_units_conj w X

theorem conjugate_mem (u : G.El) {X : G.Mat} (h : X ∈ G.lie) :
    G.conjugate u X ∈ G.lie := by
  rw [mem_lie]
  intro t
  rw [show t • G.conjugate u X = G.conjugate u (t • X) by simp [conjugate], exp_conjugate]
  obtain ⟨v, hv⟩ := (mem_lie G).mp h t
  exact ⟨u*v*u⁻¹, by simp [hv, conjugate]⟩

theorem bracket_mem {X Y : G.Mat} (h : X ∈ G.lie) (h' : Y ∈ G.lie) :
    X*Y-Y*X ∈ G.lie := by
  let a := fun t : ℝ => exp (t • X)
  let f := fun t : ℝ => a t * Y * star (a t)
  have hall (t : ℝ) : f t ∈ G.lie := by
    obtain ⟨u, hu⟩ := (mem_lie G).mp h t
    simpa only [f, a, conjugate, ← hu] using G.conjugate_mem u h'
  have he : HasDerivAt a X 0 := by
    simpa [a] using! hasDerivAt_exp_smul_const X (0 : ℝ)
  have H : HasDerivAt f (X*Y-Y*X) 0 := by
    have d := (he.mul_const Y).mul he.star
    have ha : a 0 = 1 := by simp [a]
    simpa only [ha, one_mul, star_one, G.generates_skew h, mul_one,
      mul_neg, sub_eq_add_neg] using! d
  apply G.closed_lie.mem_of_tendsto H.tendsto_slope
  filter_upwards with t
  rw [slope_def_module]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hall _) (hall _))

/-- Real simplicity with the nonabelian clause. -/
def Simple : Prop :=
  (∃ X ∈ G.lie, ∃ Y ∈ G.lie, X*Y-Y*X ≠ 0) ∧
  ∀ I : Submodule ℝ G.Mat, I ≤ G.lie → (∀ X ∈ G.lie, ∀ Y ∈ I, X*Y-Y*X ∈ I) →
    I = ⊥ ∨ I = G.lie

end YM.Gauge
