import YM.Extra.WILSON_STARTUP.Cylinder

/-!
# Initial source cap before any propagation

True unmasked cylinder sup for the part inserted in flag packets, paid by a
strong enough K-smallness after actual t^{-l} and before profile changes.
Paper's `thick` and terminally normalized comparison will use the SAME
coordinate sizes even if a_N^{-d} diverges afterwards. No finite limiting
beta or terminal map assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Mark
open Function Filter RG Wilson Lattice Source Work
open scoped Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {n : Side} {A : Hol G}

def slotOrder (F : Labels.Frame G d) := ∑ i : F.Index, (F.grades i).2

private lemma whole (C : SectionData F) : ∃ c : ℝ, 1 ≤ c ∧ ∀ v : F.Coeff, ∀ U : CoverConfig G,
    ‖C.evaluate v U‖ ≤ F.coeffSize v*c := by
  have he (i : F.Index) := (isCompact_range (C.continuous_evaluate (Pi.single i 1)).norm).bddAbove
  choose c h using he
  have hc (i) (U) := h i ⟨U,rfl⟩
  have hn (i) := (norm_nonneg _).trans (hc i 1)
  let w := 1+∑ i,c i
  refine ⟨w,le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hn i),fun v U => ?_⟩
  let e : F.Coeff →ₗ[ℂ] ℂ := {
    toFun x := C.evaluate x U
    map_add' x y := congr_fun (C.eval_linear.map_add x y) U
    map_smul' x y := congr_fun (C.eval_linear.map_smul x y) U }
  have hU : C.evaluate v U = ∑ i : F.Index, v i * C.evaluate (Pi.single i 1) U := by
    change e v = ∑ i, v i • e _
    simp_rw [← e.map_smul, ← map_sum]; apply congr_arg e; ext1 i; simp [Pi.single_apply]
  rw [hU, Labels.Frame.coeffSize, Finset.sum_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]; gcongr
  exact (hc i U).trans ((Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one))

def price (C : SectionData F) := (whole C).choose

theorem price_ge_one (C : SectionData F) : 1 ≤ price C := (whole C).choose_spec.1

def scale (C : SectionData F) (b : BudgetPoint) := (b.threshold⁻¹)^slotOrder F * price C

theorem scale_pos (C : SectionData F) (b : BudgetPoint) : 0 < scale C b :=
  mul_pos (pow_pos (inv_pos.mpr b.threshold_pos) _) (lt_of_lt_of_le one_pos (price_ge_one C))

theorem coeff_nn (v : F.Coeff) : 0 ≤ F.coeffSize v := Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma whole_scaled (C : SectionData F) (b : BudgetPoint) (v : F.Coeff) (U : CoverConfig G) :
    ‖C.evaluate (F.scaled b.threshold⁻¹ v) U‖ ≤ scale C b * F.coeffSize v := by
  let t := b.threshold⁻¹
  have ht : 1 ≤ t := (one_le_inv₀ b.threshold_pos).mpr b.threshold_le
  calc
    _ ≤ F.coeffSize _ * price C := (whole C).choose_spec.2 _ _
    _ ≤ (∑ i, t ^ slotOrder F * ‖v i‖) * price C := by
      gcongr
      · exact zero_le_one.trans (price_ge_one C)
      unfold Labels.Frame.coeffSize; gcongr with i
      have := b.threshold_pos
      simp only [Labels.Frame.scaled_apply,norm_mul, Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ b.threshold⁻¹ ^ (F.grades i).2)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht (Finset.single_le_sum (fun i _ => Nat.zero_le (F.grades i).2) (Finset.mem_univ i))) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, scale,Labels.Frame.coeffSize]; unfold t; ring

theorem fees (C : SectionData F) (ha : C.Sound A) (o : Site n) (R : Rep G n) (v : F.Coeff)
    {w a : ℝ} (hk : R.activities.KBound R.p w) (ha' : 0 < a) (hw : w * scale C R.p ≤ a) :
    (entry C o R v).remBound o R a (F.coeffSize (F.core v)) := by
  obtain ⟨f,hf,h⟩ := hk
  let c := F.coeffSize (F.core v)
  have hc := coeff_nn (F.core v)
  let p := scale C R.p * c
  have hp : 0 ≤ p := mul_nonneg (scale_pos C R.p).le hc
  let Y := C.footprint o
  let A := R.activities
  have ho : o ∈ Y := Finset.mem_image.mpr ⟨0,ha.anchored,by simp⟩
  let s := fun i => if o∈(A.forced i).support then f i*p else 0
  let σ := fun i => if o∈(A.forced i).support then R.p.mass (A.forced i).support (f i) else 0
  have hnn (i) : 0 ≤ s i := by unfold s; split <;> first | exact le_rfl | exact mul_nonneg (hf i).1 hp
  have h' : SumBudget σ w := h o
  have he : (fun i => R.p.mass (A.forced i).support (s i)) = fun i => σ i*p := by
    funext i; simp [s,σ,BudgetPoint.mass,mul_ite,ite_mul,mul_assoc]
  refine ⟨0,c,le_rfl,hc,by simp [c],ha',⟨fun _ => 0, ?_, fun i => ⟨le_rfl, fun U _ l _ _ => ?_⟩⟩, ⟨s,?_⟩⟩
  · simp_rw [BudgetPoint.mass,mul_zero]; exact ⟨fun _ => le_rfl,summable_zero,tsum_zero.le⟩
  · change ‖leftDerivs (fun _ => (0:ℂ)) l U‖ ≤ 0; simp [G07.left_const]
  refine ⟨?_,fun i => ⟨hnn i,fun U => ?_⟩⟩
  · change SumBudget (fun i => R.p.mass (A.forced i).support (s i)) (a*c)
    rw [he]; exact ⟨fun i => mul_nonneg (h'.1 i) hp,h'.2.1.mul_right p,(tsum_mul_right.trans_le
      (mul_le_mul_of_nonneg_right h'.2.2 hp)).trans ((mul_assoc ..).symm.trans_le (mul_le_mul_of_nonneg_right hw hc))⟩
  · change ‖inscription C o R v i U‖ ≤ _
    unfold inscription; split
    next hg =>
      rw [show s i = _ from if_pos (hg.2 ho), norm_mul, Complex.norm_real]
      exact mul_le_mul ((hf i).2 U) (whole_scaled C R.p (F.core v) (expandAt o U)) (norm_nonneg _) (hf i).1
    rw [norm_zero]; exact hnn _
end YM.WilsonStartup.Mark
