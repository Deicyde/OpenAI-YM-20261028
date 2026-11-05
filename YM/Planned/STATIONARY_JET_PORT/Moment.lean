import YM.Next.FOUNDATIONS.SU2
import YM.Progress.STATIONARY_SCENES.Frames
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.Push.STATIONARY_UNIFORM.Touch

set_option warningAsError false
/-!
# Absolute prices (not pointwise only)

This port does not yet use translation equivariance or momentum conservation
(even repeated sites and completely irregular trees). In position units
including exponentials, genuine row & column weights at a fraction of rate,
and source sums suitable e.g. for normalized real waves. No factor of
matrix or torus dimension in the derivative row/col prices. In the
extensive scalar price pay one number of sites (volume, NOT volume^k).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Filter Function Metric Lattice Matrix Push.Uniform RG
 
open scoped Topology ContDiff BigOperators Classical

variable {ι σ τ : Type} [Fintype ι] {n : Side} {k K N : ℕ} {l : ι → Site n} {a C : ℝ}

/-- Convenient common counting purchase, positive and tame also in the order
zero / no-index cases. -/
def rollCall (a : ℝ) (K k : ℕ) := (1+(K:ℝ)*countCost a)^k
lemma roll_pos (ha : 0<a) (K k : ℕ) : 0<rollCall a K k := by have h := count_pos ha; unfold rollCall; positivity


lemma checkSum (K k : ℕ) (h : Multiplicity l K) (ha : 0<a) (y : Site n) :
    ∑ q : Fin k → ι, glaze l y q a ≤ rollCall a K k := by
  let F (_ : Fin k) (i : ι) := Decay a y (l i)
  simp_rw [glaze_prod]
  change ∑ q : Fin k → ι, (∏ i, F i (q i)) ≤ _
  rw [← Fintype.prod_sum]; unfold F; rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => (decay_pos ..).le)) _ _
  exact (h.count l ha y).trans (le_add_of_nonneg_left zero_le_one)

omit [Fintype ι] in
lemma splitPrice (l : ι → Site n) (x : Site n) (q : Fin k → ι) (a : ℝ) : glaze l x q a = glaze l x q (a/2) * glaze l x q (a/2) := by
  unfold glaze; rw [← Real.exp_add]; congr 1; ring

-- true derivative price (entrywise also certifies arbitrary superpositions
-- with the matching coefficients, at exactly this p, all oriented slots).




-- Include both directions for arbitrary inverse responses. `.coefficient`
-- similarly gives both rows. For fixed k also apply `wire_moment` or this
-- bound directly to `Cable.switch`. Symbols remain at the ACTUAL positions.


/-- Extensive sum of genuine polarized scalar entries of ANY Scatter
(coarse or fine). No all-to-all loss. For a better constant can save one
count factor by dropping rooted slot. No k=0 promise from Scatter. -/
lemma per_volume {f : Positions ι → ℝ} {x : Positions ι}
    (h : Scatter l a N f x C) (hc : 0 ≤ C) (ha : 0<a) (hL : Multiplicity l K) (hk : k ≤ N) (t : Fin k) :
    ∑ q : Fin k → ι, |entry f x q| * (glaze l (l (q t)) q (a/2))⁻¹ ≤
      (Fintype.card ι:ℝ)*C*rollCall (a/2) K k := by
  let v := a/2
  have hr (q : Fin k → ι) : |entry f x q| *(glaze l (l (q t)) q v)⁻¹ ≤ ∑ i, C*glaze l (l i) q v := by
    let U := glaze l (l (q t)) q v; have hU : 0<U := Real.exp_pos _
    apply le_trans _ (Finset.single_le_sum (f:=fun i => C*glaze l (l i) q v) (fun i _ => mul_nonneg hc (Real.exp_pos _).le) (Finset.mem_univ (q t)))
    have ht : |entry f x q| ≤ C*glaze l (l (q t)) q a := h k hk q t
    rw [splitPrice] at ht
    rw [← div_eq_mul_inv, div_le_iff₀ hU]
    simpa only [v, mul_assoc] using ht
  refine (Finset.sum_le_sum (fun i _ => hr i)).trans ?_
  rw [Finset.sum_comm]
  apply le_trans (b:=∑ _ : ι, C*rollCall (a/2) K k) (Finset.sum_le_sum (fun i _ => ?_))
  · rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]
  rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (checkSum K k hL (half_pos ha) (l i)) hc

lemma invoice {f : Positions ι → ℝ} {x : Positions ι}
    (h : Scatter l a N f x C) (hc : 0 ≤ C) (ha : 0<a) (hL : Multiplicity l K) (hk : k ≤ N) (t : Fin k)
    (v : Fin k → Positions ι) :
    |iteratedFDeriv ℝ k f x v| ≤ (Fintype.card ι:ℝ)*C*rollCall (a/2) K k * ∏ i, ‖v i‖ := by
  let M := ∏ i, ‖v i‖; have hM : 0 ≤ M := Finset.prod_nonneg fun i _ => norm_nonneg _
  rw [multi_expansion]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply le_trans _ (mul_le_mul_of_nonneg_right (per_volume h hc ha hL hk t) hM)
  rw [Finset.sum_mul]; refine Finset.sum_le_sum fun q _ => ?_
  rw [abs_mul,mul_comm]
  let P := (∏ i, v i (q i))
  let Z := glaze l (l (q t)) q (a/2)
  have hP : |P| ≤ M := by
    change ‖P‖ ≤ _; unfold P; rw [norm_prod]; exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_le_pi_norm ..
  change |entry f x q| * |P| ≤ _
  have h : 0<Z := Real.exp_pos _
  have ht : 1 ≤ Z⁻¹ := (one_le_inv₀ h).mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (by positivity)) (by positivity)))
  exact mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) ht) hP (abs_nonneg _)
    (mul_nonneg (abs_nonneg _) (inv_pos.mpr h).le)

end YM.Planned.JetPort
