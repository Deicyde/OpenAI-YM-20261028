import YM.Push.LOOP_COEFFICIENT.Block.Magnitude
import YM.Push.LOOP_COEFFICIENT.Block.Tests
import YM.Push.LOOP_COEFFICIENT.Fine.Inverses

/-!
# Alias duality exchanges and cost
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Matrix Set Filter Lattice Laurent RG Wilson Bloch Complex Portal
open scoped Topology BigOperators Matrix.Norms.L2Operator ContDiff
variable {L : Side} {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [Fintype d] {v u : Weight L} {q : Momentum} {C D η : ℝ}

omit [DecidableEq a] in lemma rev_mag (x : CSpace (Co L a)) : ∑ i : Site L,(mag (beam (-i) x))^2 = mag x ^2 := (Equiv.sum_comp (Equiv.neg (Site L)) (fun i => mag (beam i x)^2)).trans (mag_prod x)
omit [DecidableEq a] [DecidableEq b] in lemma one_cauchy (x : CSpace (Co L a)) (y : CSpace (Co L b)) : ∑ i : Site L,mag (beam (-i) x) * mag (beam i y) ≤ mag x * mag y := by
  apply le_of_sq_le_sq _ (mul_nonneg (mag_nonneg x) (mag_nonneg y)); convert! Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => mag (beam (-i) x)) (fun i => mag (beam i y)) using 1; rw [mul_pow,rev_mag]; erw [mag_prod y]











variable (v u) (hv : ∀ q i,0<v q i) (hu : ∀ q i,0<u q i) (X : Vertex c a b) (Y : Profiles L c d)
omit [Fintype c] in
lemma induced_base (hc : 0 ≤ C) (h : ∀ i, v (-q) (-i)*u q i * ‖X.base (aliasAt q i)‖ ≤ C) :
    ‖(weigh (distributed L a v hv).dual (distributed L b u hu) (induce X Y)).base q‖ ≤ C := by
  refine op_of_bil _ hc fun x y => ?_; rw [base_pair]; apply (norm_sum_le ..).trans
  let f (i : Site L) := mag (beam (-i) x) * mag (beam i y)
  have he (i : Site L) : 0≤v (-q) (-i)*u q i := mul_nonneg (hv _ _).le (hu _ _).le
  calc
    _ ≤ ∑ i,C * f i := Finset.sum_le_sum fun i _ => by rw [norm_mul, Complex.norm_real,Real.norm_of_nonneg (he i)]; exact (mul_le_mul_of_nonneg_left (mag_pair ..) (he i)).trans (by unfold f; rw [mul_assoc ‖_‖,← mul_assoc]; exact mul_le_mul_of_nonneg_right (h i) (mul_nonneg (mag_nonneg _) (mag_nonneg _)))
    _ ≤ _ := by rw [← Finset.mul_sum, mul_assoc]; exact mul_le_mul_of_nonneg_left (one_cauchy x y) hc

omit [DecidableEq b] [Fintype b] [Fintype c] in
lemma induced_gap (X : Vertex c a a) (hC : 0<C) (h : ∀ i, Fine.Gap (X.base (aliasAt q i)) (C / (v (-q) (-i)*u q i))) :
    Fine.Gap ((weigh (distributed L a v hv).dual (distributed L a u hu) (induce X Y)).base q) C := by
  intro x; rw [Matrix.toLpLin_apply]
  change C*mag x.ofLp ≤ mag (_ *ᵥ _); refine le_of_sq_le_sq ?_ (mag_nonneg _)
  rw [mul_pow, ← mag_prod, Finset.mul_sum, ← rev_mag]; apply Finset.sum_le_sum; intro i hi
  have hh := mul_pos (hv (-q) (-i)) (hu q i)
  rw [base_action, mag_smul,← mul_pow, Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  have he := h i (WithLp.toLp 2 (beam i x.ofLp)); change (C / _) * mag (beam _ _) ≤ mag (_ *ᵥ _) at he
  exact pow_le_pow_left₀ (mul_nonneg hC.le (mag_nonneg _)) (by rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)] at he; rwa [mul_comm (v _ _ * _ )]) _
end YM.Push.Loops.Block
