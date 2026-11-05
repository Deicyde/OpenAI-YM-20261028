import YM.Push.LOOP_COEFFICIENT.Block.Exchange
import YM.Push.LOOP_COEFFICIENT.Block.Masses

/-!
# Distributed weighted gap on complete fine vertices and scarcity of infrared columns
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Set Filter Matrix Metric Lattice Laurent RG Precision Exterior Bloch Bid Wilson Kernel Complex Portal
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {G : Gauge} {L : Side} {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b]
    {η C g σ : ℝ} {H : Bed} {p : Momentum}

def lower (L : Side) (a : Type) [Fintype a] [DecidableEq a] := distributed L a (fun p i => (energy L p i)⁻¹) fun p i => inv_pos.mpr (energy_pos L p i)


lemma energy_sum (η : ℝ) : ∃ K>0, ∀ {L : Side}, Odd L.val → ∀ p∈Tube η, ∑ i, ((L.val*energy L p i)⁻¹)^6 ≤ K := by
  obtain ⟨K,hK,H⟩ := mass_sum
  refine ⟨2^6 * K, by positivity,fun {L} hL p hp => ?_⟩
  obtain ⟨z,hz,x,rfl⟩ := center_adjust hp
  simp only [energy_shift]; rw [show ∑ i : Site L,((L.val*energy L z (i+wrap L x))⁻¹)^6 = ∑ i,((L.val*energy L z i)⁻¹)^6 from Equiv.sum_comp (Equiv.addRight (wrap L x)) (fun i => ((L.val*energy L z i)⁻¹)^6)]
  calc
    _ ≤ ∑ i : Site L,(2*(mass i)⁻¹)^6 := Finset.sum_le_sum fun i _ => by
      have h₁ := energy_center hz hL i; have h₂ := energy_pos L z i; have h₃ : 0 < mass i := by unfold mass; positivity
      gcongr; rw [← div_eq_mul_inv]; apply inv_le_of_inv_le₀ (by positivity); rw [inv_div]; rw [div_le_iff₀ (side_pos _)] at h₁; rw [div_le_iff₀ zero_lt_two]; linarith
    _ ≤ _ := by simp_rw [mul_pow,← Finset.mul_sum]; gcongr; exact H L

lemma alias_holds (hL : Odd L.val) (h : Fine.Holds G H η g) (hp : p∈Tube η) (i : Site L) : Fine.Gap (Fine.proxy G H (L.val:ℝ)⁻¹ (aliasAt p i)) (g/4 * energy L p i ^2) ∧ Fine.Gap ((Fine.gauged G (L.val:ℝ)⁻¹).base (aliasAt p i)) (g/4*energy L p i ^2) := by
  obtain ⟨q,hq,x,rfl⟩ := center_adjust hp
  obtain ⟨y,hy⟩ := alias_shift i q x
  rw [hy,energy_shift,Fine.proxy_period,Fine.gauged_period]
  let z := aliasAt q (i+wrap L x)
  have hw := Fine.center_window (z:=z) ⟨alias_tube _ hq.1,alias_core hL _ hq⟩
  let μ := (L.val:ℝ)⁻¹
  have hm : μ≤1 := inv_le_one_of_one_le₀ (by exact_mod_cast L.pos)
  have hμ : 0<μ := inv_pos.mpr (side_pos L)
  obtain ⟨he,hf⟩ := h.spectrum hw hμ hm (z:=z) (mem_ball.mpr ((Fine.shade_dist (div_pos h.width (side_pos _)) (alias_tube _ hq.1)).trans_le (by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg (Fine.shade z))) h.width.le)))
  have h₁ := energy_pos L q (i+wrap L x); have h₂ := energy_ruler q (i+wrap L x)
  have ht : _ ≤ g*Fine.ruler μ (Fine.shade z)^2 := show g/4*energy L q (i+wrap L x)^2 ≤ _ from (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h₁.le h₂ 2) (show 0≤g/4 by linarith [h.lower])).trans_eq (by unfold μ z; ring)
  exact ⟨he.mono ht,hf.mono ht⟩

variable {Y : Profiles L a c} {X X' : Vertex a b b}
omit [DecidableEq a] [Fintype a] in
lemma induce_lower_gap (hg : 0<g) (h : ∀ i : Site L, Fine.Gap (X.base (aliasAt p i)) (g * energy L p i ^2)) : Fine.Gap ((weigh (lower L b).dual (lower L b) (induce X Y)).base p) g := by
  apply induced_gap _ _ _ _ Y X hg; intro i; rw [energy_neg]; apply (h i).mono (by rw [← mul_inv, div_inv_eq_mul, pow_two])

variable {T : Profiles L (Axes G) (Axes G)} {q : Clip} {W : PathData G}


end YM.Push.Loops.Block
