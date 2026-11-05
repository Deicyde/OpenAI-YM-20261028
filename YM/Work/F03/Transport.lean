import Mathlib.Analysis.Normed.Group.Tannery
import YM.Analysis.Polydisc
import YM.PREC.Derivative


/-!
# Real ray limits, along the links and through the path sums

All at a fixed torus. In the real ray test the long transporter acts isometrically.
So we can read these leading terms even without having uniform analyticity bounds: a
common bound for finitely many rescaled plaquette curvatures suffices to dominate all
the rescaled slots. No truncation/mask is involved.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.F03
open Filter Lattice RG Wilson Precision Push Exterior
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

variable {G : Gauge} {n : Side}

/-- Including the /2 in the price, with *physical* color metric. -/
lemma price_limit {V : ℝ → G.El} (h : V 0 = 1) {c : G.Color}
    (hc : HasDerivAt (fun t => G.mat (V t)) (G.colorMat c) 0) :
    Tendsto (fun t : ℝ => G.price (V t) / t ^ 2) (𝓝[≠] 0) (𝓝 (‖c‖ ^ 2 / 2)) := by
  have hm : Tendsto (fun t : ℝ => t⁻¹ • (G.mat (V t) - 1)) (𝓝[≠] 0) (𝓝 (G.colorMat c)) := by
    simpa only [zero_add, h, G.mat_one] using! (hasDerivAt_iff_tendsto_slope_zero.mp hc)
  have he := (hm.norm.div_const G.colorScale).pow 2
  rw [G.colorMat_norm, mul_div_cancel_left₀ _ G.colorScale_pos.ne'] at he
  refine (he.div_const 2).congr' (Filter.Eventually.of_forall fun t => ?_)
  change (‖t⁻¹ • (G.mat (V t) - 1)‖ / _) ^ 2 / 2 = G.price _ / _
  rw [norm_smul, mul_div_assoc]
  change (‖t⁻¹‖ * G.chord _) ^ 2 / 2 = _
  rw [mul_pow, G.chord_price, Real.norm_eq_abs, sq_abs, inv_pow]
  ring

/-- The leading curvature also only depends on the mat tangent. -/
lemma curvature_of_hasDerivAt {V : ℝ → G.El} {c : G.Color}
    (hc : HasDerivAt (fun t => G.mat (V t)) (G.colorMat c) 0) :
    HasDerivAt (fun t => G.curvature (V t)) c 0 := by
  -- as in `G.leading_curvature`
  let A := fun t : ℝ => G.mat (V t)
  let P : ℝ → G.Mat := fun t => (1/2 : ℝ) • (A t - star (A t))
  have hB : HasDerivAt P (G.colorMat c) 0 := by
    have he := (hc.sub hc.star).const_smul (1/2 : ℝ)
    rw [G.colorMat_skew, sub_neg_eq_add, ← two_smul ℝ, smul_smul,
      div_mul_cancel₀ _ (two_ne_zero), one_smul] at he
    exact he
  simp_rw [Gauge.curvature, G.mat_inv]
  have he : HasDerivAt (fun t => G.projectColor (P t)) (G.projectColor (G.colorMat c)) 0 :=
    G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hB
  rw [G.project_colorMat] at he
  exact he

abbrev faceCurl (b : Face (Per n)) (a : fieldDir G n 1) := dColor G n 1 a (b.1,plaquette b.2)

lemma face_deriv (x : Face (Per n)) (a : fieldDir G n 1) :
    HasDerivAt (fun t : ℝ => G.mat (faceValue (represent (t • a)) x))
      (G.colorMat (faceCurl x a)) 0 := by
  rw [faceCurl, ← fundamental]
  exact travell (square _ _) x.1 a

/-- Site of the actual plaquette read (modulo period). -/
def slotFace (s : Slot) (x : Site n) : Face (Per n) := (wrap n s.offset + x, s.plaq)

lemma atSite_path (s : Slot) (U : Config G n) (x : Site n) :
    s.atSite U x = G.adjoint (travel U x s.walk) (G.curvature (faceValue U (slotFace s x))) := by
  unfold Slot.atSite Slot.eval
  rw [travel_at, map_zero, zero_add, show faceValue _ _ = _ from
    (show faceValue (expandAt x U) (s.offset,s.plaq) = faceValue U (slotFace s x) from travel_at ..)]

lemma slot_deriv (s : Slot) (x : Site n) (a : fieldDir G n 1) :
    HasDerivAt (fun t : ℝ => s.atSite (represent (t • a)) x) (faceCurl (slotFace s x) a) 0 := by
  let M (t : ℝ) := faceValue (represent (t • a)) (slotFace s x)
  let T (t : ℝ) := travel (represent (t • a)) x s.walk
  have ht : HasDerivAt (fun t => G.mat (T t)) (G.colorMat (linkSum (collect G a) x s.walk)) 0 :=
    travell s.walk x a
  have hf := face_deriv (slotFace s x) a
  have hz : T 0 = 1 := by unfold T; rw [zero_smul]; exact stroll_zero ..
  have hv : M 0 = 1 := by unfold M; rw [zero_smul]; exact stroll_zero ..
  simp_rw [atSite_path, ← G.curvature_conjugate]
  refine curvature_of_hasDerivAt (V := fun t => T t * M t * (T t)⁻¹) ?_
  change HasDerivAt (fun t => G.mat (M t)) _ 0 at hf
  simp only [G.mat_mul, G.mat_inv]
  convert! (ht.mul hf).mul ht.star using 1
  simp [hz, hv, G.colorMat_skew]

lemma slot_limit (s : Slot) (x : Site n) (a : fieldDir G n 1) :
    Tendsto (fun t : ℝ => t⁻¹ • s.atSite (represent (t • a)) x) (𝓝[≠] 0)
      (𝓝 (faceCurl (slotFace s x) a)) := by
  have hh : s.atSite (represent ((0:ℝ) • a)) x = 0 := by
    rw [atSite_path, zero_smul, show faceValue (represent (0:fieldDir G n 1)) (slotFace s x) = 1 from stroll_zero .., G.curvature_unit, map_zero]
  simpa only [hh, zero_add, sub_zero] using
    (hasDerivAt_iff_tendsto_slope_zero.mp (slot_deriv s x a))

/-- No volume uniformity. Uniform over *all* slots including arbitrary winding. -/
lemma slots_bound (a : fieldDir G n 1) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ (x : Site n) (s : Slot),
      ‖t⁻¹ • s.atSite (represent (t • a)) x‖ ≤ B := by
  let B := 1 + ∑ b : Face (Per n), ‖faceCurl b a‖
  refine ⟨B, by unfold B; positivity, ?_⟩
  have hv (b : Face (Per n)) :
      ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖t⁻¹ • G.curvature (faceValue (represent (t • a)) b)‖ < B := by
    have he : Tendsto (fun t : ℝ => t⁻¹ • G.curvature (faceValue (represent (t • a)) b))
        (𝓝[≠] 0) (𝓝 (faceCurl b a)) := by
      have hz : G.curvature (faceValue (represent ((0:ℝ) • a)) b) = 0 := by
        rw [zero_smul, show faceValue (represent (0:fieldDir G n 1)) b = 1 from stroll_zero .., G.curvature_unit]
      simpa only [zero_add, hz, sub_zero] using
        (hasDerivAt_iff_tendsto_slope_zero.mp (curvature_of_hasDerivAt (face_deriv b a)))
    exact he.norm.eventually (gt_mem_nhds ((Finset.single_le_sum
      (f := fun b : Face (Per n) => ‖faceCurl b a‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ b)).trans_lt (by unfold B; linarith)))
  filter_upwards [eventually_all.mpr hv] with t ht x s
  rw [atSite_path, ← map_smul, G.norm_adjoint]
  exact (ht (slotFace s x)).le

lemma row_abs_summable (W : PathData G) {p σ C Λ} (hb : W.Bounds p σ C Λ) (b : PlaqAxes) :
    Summable fun i => |(W.row b i).1| := by
  refine Summable.of_nonneg_of_le (fun i => abs_nonneg _) ?_ (hb.rows b).2.1
  intro i
  exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hb.width.le (by positivity)))

def ellLine (W : PathData G) (b : Face (Per n)) (a : fieldDir G n 1) : G.Color :=
  ∑' i, (W.row b.2 i).1 • faceCurl (slotFace (W.row b.2 i).2 b.1) a

lemma ellLine_summable (W : PathData G) {p σ C Λ} (hb : W.Bounds p σ C Λ)
    (b : Face (Per n)) (a : fieldDir G n 1) :
    Summable fun i => (W.row b.2 i).1 • faceCurl (slotFace (W.row b.2 i).2 b.1) a := by
  refine Summable.of_norm_bounded ((row_abs_summable W hb b.2).mul_right
    (∑ b : Face (Per n), ‖faceCurl b a‖)) ?_
  intro i
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum
    (f := fun b : Face (Per n) => ‖faceCurl b a‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ _)) (abs_nonneg _)

lemma ell_limit (W : PathData G) {p σ C Λ} (hb : W.Bounds p σ C Λ)
    (b : Face (Per n)) (a : fieldDir G n 1) :
    Tendsto (fun t : ℝ => t⁻¹ • W.ell (represent (t • a)) b) (𝓝[≠] 0)
      (𝓝 (ellLine W b a)) := by
  obtain ⟨B, hB, hv⟩ := slots_bound a
  simp_rw [PathData.ell, ← tsum_const_smul'', PathData.ellTerms, smul_comm (Inv.inv _)]
  refine tendsto_tsum_of_dominated_convergence ((row_abs_summable W hb b.2).mul_right B)
    (fun i => (slot_limit (W.row b.2 i).2 b.1 a).const_smul _) ?_
  filter_upwards [hv] with t ht i
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (ht b.1 _) (abs_nonneg _)


section atoms
variable {k : ℕ} (A : Atom G k)

lemma poly_bound (x : Fin k → G.Color) (c : ℝ) (h : ∀ i, ‖x i‖ ≤ c) :
    |A.poly x| ≤ A.magnitude * c ^ k := by
  -- Generalized from `Atom.unmasked_bound` to the rescaled arguments.
  have hh i j : |x i j| ≤ c := calc
    _ = |inner ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ j) (x i)| := by
      simp only [EuclideanSpace.basisFun_inner]
    _ ≤ _ := (abs_real_inner_le_norm _ _).trans (by
      rw [OrthonormalBasis.norm_eq_one, one_mul]
      exact h i)
  unfold Atom.poly Atom.magnitude
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, Finset.abs_prod]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  convert Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => hh j (i j)) using 1
  simp

lemma poly_homog (x : Fin k → G.Color) (c : ℝ) :
    A.poly (fun i => c • x i) = c ^ k * A.poly x := by
  unfold Atom.poly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  ring

lemma atom_scale (x : Site n) (a : fieldDir G n 1) (t : ℝ) :
    A.unmasked (represent (t • a)) x / t ^ k =
      A.poly fun j => t⁻¹ • (A.leg j).atSite (represent (t • a)) x := by
  rw [poly_homog A, inv_pow, Atom.unmasked, div_eq_inv_mul]

lemma atom_limit (x : Site n) (a : fieldDir G n 1) :
    Tendsto (fun t : ℝ => A.unmasked (represent (t • a)) x / t ^ k) (𝓝[≠] 0)
      (𝓝 (A.poly fun j => faceCurl (slotFace (A.leg j) x) a)) := by
  simp_rw [atom_scale]
  have ht : Tendsto (fun t : ℝ => fun j => t⁻¹ • (A.leg j).atSite (represent (t • a)) x)
      (𝓝[≠] 0) (𝓝 fun j => faceCurl (slotFace (A.leg j) x) a) :=
    tendsto_pi_nhds.mpr fun j => slot_limit _ _ _
  exact ((show Continuous A.poly by unfold Atom.poly; fun_prop).tendsto _).comp ht

lemma atoms_limit (a : fieldDir G n 1) (M : ℕ → Atom G k) {σ C : ℝ} (hs : 0 < σ)
    (hb : SumBudget (fun i => (M i).budget σ) C) :
    Tendsto (fun t : ℝ => uncut M (represent (t • a)) / t ^ k) (𝓝[≠] 0)
      (𝓝 (∑ x : Site n, ∑' i, (M i).poly fun j => faceCurl (slotFace ((M i).leg j) x) a)) := by
  unfold uncut
  simp_rw [Finset.sum_div, ← tsum_div_const]
  refine tendsto_finsetSum _ (fun x hx => ?_)
  obtain ⟨B, hB, hv⟩ := slots_bound a
  apply tendsto_tsum_of_dominated_convergence (hb.2.1.mul_right (B ^ k))
    (fun i => atom_limit _ _ _)
  filter_upwards [hv] with t ht i
  rw [atom_scale (M i), Real.norm_eq_abs]
  refine (poly_bound (M i) _ B (fun j => ht x _)).trans ?_
  exact mul_le_mul_of_nonneg_right ((M i).lower_budget σ hs) (pow_nonneg hB k)

lemma uncut_limit (a : fieldDir G n 1) (M : ℕ → Atom G (2+(k+1))) {σ C : ℝ}
    (hs : 0 < σ) (hb : SumBudget (fun i => (M i).budget σ) C) :
    Tendsto (fun t : ℝ => uncut M (represent (t • a)) / t ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t ^ (k+1)) (𝓝[≠] 0) (𝓝 0) := by
    simpa using! (tendsto_id (x := 𝓝 (0:ℝ))).pow (k+1) |>.mono_left
      (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hv := (atoms_limit a M hs hb).mul ht
  rw [mul_zero] at hv
  refine hv.congr' ?_
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 from self_mem_nhdsWithin] with t hn
  rw [pow_add]
  field_simp

end atoms

end YM.Work.F03
