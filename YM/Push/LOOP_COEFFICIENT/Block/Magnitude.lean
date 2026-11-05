import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Real.Pi.Bounds
import YM.Push.LOOP_COEFFICIENT.ContinuumTrace

/-!
# Absolute L² estimates in finite type spaces
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Matrix Set Function Filter Lattice Laurent RG Bloch Wilson Complex
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
def mag (x : CSpace a) := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ a)‖
omit [DecidableEq a] in lemma mag_nonneg (x : CSpace a) : 0≤mag x := by unfold mag; positivity
omit [DecidableEq a] in lemma mag_sq (x : CSpace a) : mag x ^2 = ∑ i, ‖x i‖^2 := PiLp.norm_sq_eq_of_L2 _ (WithLp.toLp 2 x)
omit [DecidableEq a] in lemma mag_bar (x : CSpace a) : mag (star x)=mag x := by rw [← sq_eq_sq₀ (mag_nonneg _) (mag_nonneg _),mag_sq,mag_sq]; simp
omit [DecidableEq a] in lemma dot_self (x : CSpace a) : star x ⬝ᵥ x = (mag x ^2:ℝ) := by rw [mag_sq]; simp [ofReal_sum,dotProduct,mul_comm,mul_conj,Complex.normSq_eq_norm_sq]
omit [DecidableEq a] in lemma mag_dot (x y : CSpace a) : ‖x ⬝ᵥ y‖ ≤ mag x * mag y := by
  rw [← mag_bar x]; simpa only [EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,star_star,dotProduct_comm y] using! norm_inner_le_norm (𝕜:=ℂ) (WithLp.toLp 2 (star x)) (WithLp.toLp 2 y)
omit [DecidableEq a] in lemma mag_op (M : Matrix a b ℂ) (x : CSpace b) : mag (M *ᵥ x) ≤ ‖M‖ * mag x := Matrix.l2_opNorm_mulVec M _
omit [DecidableEq a] in lemma op_of_mag (M : Matrix a b ℂ) {C : ℝ} (hc : 0≤C) (he : ∀ x,mag (M *ᵥ x) ≤ C * mag x) : ‖M‖ ≤ C := by rw [Matrix.l2_opNorm_def]; exact ContinuousLinearMap.opNorm_le_bound _ hc (fun x => he x.ofLp)
omit [DecidableEq a] in lemma mag_pair (M : Matrix a b ℂ) (x y) : ‖x ⬝ᵥ M *ᵥ y‖ ≤ ‖M‖ * mag x * mag y := (mag_dot ..).trans ((mul_le_mul_of_nonneg_left (mag_op ..) (mag_nonneg _)).trans_eq (by ring))
omit [DecidableEq a] in lemma op_of_bil (M : Matrix a b ℂ) {C : ℝ} (hc : 0≤C) (he : ∀ x y, ‖x ⬝ᵥ M *ᵥ y‖ ≤ C * mag x * mag y) : ‖M‖ ≤ C := op_of_mag M hc fun x => by
  have h := he (star (M *ᵥ x)) x; rw [dot_self,norm_real,Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mag_bar] at h; have hm := mag_nonneg x
  nlinarith only [h,mul_nonneg hc hm]




omit [DecidableEq a] in lemma mag_smul (z : ℂ) (x : CSpace a) : mag (z • x) = ‖z‖ * mag x := norm_smul z (WithLp.toLp 2 x : EuclideanSpace ℂ a)
omit [DecidableEq a] in lemma mag_except (x : CSpace a) (i) : ‖x i‖ ≤ mag x := PiLp.norm_apply_le (WithLp.toLp 2 x) i
omit [DecidableEq a] [DecidableEq b] in lemma mag_prod (x : CSpace (a×b)) : ∑ i,mag (fun j => x (i,j))^2 = mag x ^2 := by simp [mag_sq,Fintype.sum_prod_type]
omit [DecidableEq a] [DecidableEq b] in lemma mag_sum (x : CSpace (a⊕b)) : mag (x ∘ Sum.inl)^2 + mag (x ∘ Sum.inr)^2 = mag x ^2 := by simp [mag_sq,Fintype.sum_sum_type]
end YM.Push.Loops.Block
