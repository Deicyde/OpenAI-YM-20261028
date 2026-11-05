import YM.Gauge.Nearest

/-! Weighted Euclidean centroid comparison & uniqueness on the branch. -/

set_option autoImplicit false
noncomputable section
namespace YM.Branch

open Function Filter Set NormedSpace Submodule
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal

attribute [local instance] Gauge.frobInner

section average
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- average over vertices / orders. -/
def avg {n : Type*} [Fintype n] (f : n → X) := (Fintype.card n : ℝ)⁻¹ • ∑ i, f i

variable {n : Type*} [Fintype n]

@[simp] lemma avg_const [Nonempty n] (x : X) : avg (fun _ : n => x) = x := by
  have h : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [avg, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ h.ne', one_smul]

lemma norm_avg (f : n → X) : ‖avg f‖ ≤ avg fun i => ‖f i‖ := by
  unfold avg; rw [norm_smul]; simp only [norm_inv, Real.norm_natCast, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

lemma avg_mono {f g : n → ℝ} (h : f ≤ g) : avg f ≤ avg g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ h i) (by positivity)

lemma avg_add (f g : n → X) : avg (fun i => f i + g i) = avg f + avg g := by simp [avg, Finset.sum_add_distrib, smul_add]
lemma avg_sub (f g : n → X) : avg (fun i => f i - g i) = avg f - avg g := by simp [avg, Finset.sum_sub_distrib, smul_sub]
lemma avg_mul (x : ℝ) (f : n → ℝ) : avg (fun i => x*f i) = x * avg f := by simp [avg,← Finset.mul_sum, mul_left_comm]

lemma le_avg [Nonempty n] (f : n → ℝ) : ∃ x, f x ≤ avg f := by
  obtain ⟨x,-,hx⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  exact ⟨x,(avg_const (n := n) (f x)).symm.le.trans (avg_mono fun i ↦ hx i (Finset.mem_univ i))⟩

/-- Jensen for norm sq -/
lemma weighted (f : n → X) (w : n → ℝ) (h : ∀ i, 0 ≤ w i) (hh : ∑ i, w i = 1) :
    ‖∑ i, w i • f i‖^2 ≤ ∑ i, w i * ‖f i‖^2 := by
  have he : ‖∑ i, w i • f i‖ ≤ ∑ i, w i*‖f i‖ := by
    simpa only [norm_smul,Real.norm_of_nonneg (h _)] using! norm_sum_le (s := Finset.univ) (f := fun i => w i • f i)
  let m := ∑ i, w i*‖f i‖
  have hs (i) : 2*m*(w i*‖f i‖) - w i*m^2 ≤ w i*‖f i‖^2 := by nlinarith [mul_nonneg (h i) (sq_nonneg (m-‖f i‖))]
  apply le_trans _ (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hs i)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,hh,one_mul]
  change _ ≤ 2*m*m-m^2
  change _ ≤ m at he
  have hy := norm_nonneg (∑ i, w i • f i)
  nlinarith

lemma avg_sq [Nonempty n] (f : n → X) : ‖avg f‖^2 ≤ avg fun i => ‖f i‖^2 := by
  simpa only [avg, Finset.smul_sum, smul_eq_mul, Finset.mul_sum] using!
    weighted f (fun _ => (Fintype.card n : ℝ)⁻¹) (fun _ => by positivity) (by simp)
end average

variable {G : Gauge} {n : Type*} [Fintype n]

lemma price_diff (u v : G.El) : (G.repDim : ℝ)*(2*G.price (u*v⁻¹)) = ‖G.mat u-G.mat v‖^2 := by
  rw [← Gauge.chord_price]
  have he : 0 < G.colorScale := G.colorScale_pos
  have hh : (G.mat u-G.mat v)*G.mat v⁻¹ = G.mat (u*v⁻¹) - 1 := by rw [sub_mul, ← G.mat_mul, ← G.mat_mul, mul_inv_cancel]; simp
  rw [Gauge.chord, ← hh, Gauge.frob_mul_eq _ _ (G.mat_mul_star _)]
  change _ * (_ / G.colorScale)^2 = _
  rw [div_pow,← G.colorScale_sq]
  field_simp

lemma min_iff (w : n → ℝ) (hw : ∑ i, w i = 1) (f : n → G.El) (u : G.El) :
    G.Nearest u (∑ i, w i • G.mat (f i)) ↔ ∀ v : G.El,
      (∑ i, w i * G.price (f i * u⁻¹)) ≤ (∑ i, w i * G.price (f i * v⁻¹)) := by
  let m := ∑ i, w i • G.mat (f i)
  have hk (V : G.El) :
      (G.repDim:ℝ)*2*(∑ i,w i*G.price (f i * V⁻¹)) = (∑ i, w i*‖G.mat (f i)‖^2)-‖m‖^2+‖m-G.mat V‖^2 := by
    calc
      _ = ∑ i, w i * ((G.repDim:ℝ)*(2*G.price (f i*V⁻¹))) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ = ∑ i, w i * ‖G.mat (f i)-G.mat V‖^2 := by simp only [price_diff]
      _ = _ := by
        simp only [norm_sub_sq_real, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [← Finset.sum_mul,hw]
        unfold m
        rw [sum_inner]; simp only [real_inner_smul_left, Finset.mul_sum, one_mul]
        simp_rw [mul_left_comm (w _) 2]
        abel
  apply forall_congr'
  intro v
  have hd : 0 < (G.repDim:ℝ)*2 := mul_pos (by exact_mod_cast G.dimPos) two_pos
  change ‖m-_‖ ≤ ‖m-_‖ ↔ _
  symm; rw [← mul_le_mul_iff_right₀ hd,hk,hk, add_le_add_iff_left, sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]

lemma weighted_unique (G : Gauge) : ∃ δ : ℝ, 0 < δ ∧ ∀ (n : Type) [Fintype n],
    ∀ (w : n → ℝ), (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 → ∀ f : n → G.El,
    (∃ u : G.El, (∑ i, w i * G.price (f i * u⁻¹))<δ) → ∃! u, G.Nearest u (∑ i, w i • G.mat (f i)) := by
  obtain ⟨r,hr,H⟩ := G.nearest_tube
  have hg : 0 < (G.repDim:ℝ)*2 := mul_pos (by exact_mod_cast G.dimPos) two_pos
  refine ⟨r^2/((G.repDim:ℝ)*2),by positivity,fun n _ w hw hb f ⟨u,hu⟩ => H _ u ?_⟩
  apply (sq_lt_sq₀ (norm_nonneg _) hr.le).1
  calc
    _ = ‖∑ i, w i • (G.mat (f i)-G.mat u)‖^2 := by
      simp_rw [smul_sub]; rw [Finset.sum_sub_distrib, ← Finset.sum_smul,hb]; simp only [one_smul]
    _ ≤ _ := weighted (fun i => G.mat (f i)-G.mat u) w hw hb
    _ < _ := by
      simp only [← price_diff, ← mul_assoc (G.repDim:ℝ), mul_comm ((G.repDim:ℝ)*2)]
      simpa only [Finset.sum_mul, mul_assoc (w _)] using (lt_div_iff₀ hg).mp hu
end YM.Branch
