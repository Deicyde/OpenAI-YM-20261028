import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Canvas

/-! Direction costs from the patch gauge (before comparing the mean).
Caller may be normalized at another origin on this period. Never shrink a
patch according to a vanishing derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Metric Lattice Wilson Pressure RG Tree Next Next.Fluctuations Next.SectorChange
   Exterior Bloch Bid AnalyticBridge.SectorAffine.Offset Push.Uniform Planned.AtomRegular.Foliage
open WardBin.Lies
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {P : BudgetPoint} {V : Config G c} {g : Site c → G.El} {Y : Support c} {o p : Site c} {r l n : ℕ}
    {C : ℝ} {A : Slab G c l}

lemma spine_triangle {n : Side} (x y z : Site n) (p : ℕ) : spine p x z ≤ spine p x y * spine p y z := by
  unfold spine; rw [← mul_pow]; gcongr
  have ht : (separation x z:ℝ) ≤ (separation x y:ℝ)+ separation y z := by exact_mod_cast separation_triangle x y z
  have he : 0≤ (separation x y:ℝ)*(separation y z:ℝ) := by positivity
  linarith only [he,ht]

abbrev loom (P : BudgetPoint) (r : ℕ) (C : ℝ) := C*P.threshold*(1+(r:ℝ))^P.power

variable (hq : Canvas P o r V g n C) (h : ∀ i, P.dirBound p (A i)) (hC : 1 ≤ C) (hl : l ≤ n)

namespace Canvas
include hq hC
lemma paid : ‖crop o r g V‖ ≤ loom P r C := by
  have hp := P.threshold_pos
  refine (pi_norm_le_iff_of_nonneg (show 0 ≤ loom P r C by unfold loom; positivity)).mpr fun i => ?_
  by_cases hi : separation o i.1 ≤ r
  · apply (hq.size i hi).trans; unfold loom; gcongr ?_*?_
    exact (add_le_add_right (Nat.cast_le (α:=ℝ) |>.mpr hi) (1:ℝ)).trans (le_self_pow₀ (by simp) (by have := P.power_ge; omega))
  rw [crop,if_neg hi,norm_zero]; unfold loom; positivity
include h hl
lemma cost {j : ℕ} (hj : j ≤ n) (h₀ : 1 ≤ j) (v : Fin j → Panels l) (he : ∀ a, ‖v a‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (launch V o r g A) 0 v‖ ≤ (loom P r C)^j * (spine P.power o p)^j := by
  have hp := P.threshold_pos; have ht := spine_pos P.power o p
  refine (pi_norm_le_iff_of_nonneg (show 0 ≤ (loom P r C)^j * (spine P.power o p)^j by unfold loom; positivity)).mpr fun i => ?_
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond c => G.Color) i
  rw [show iteratedFDeriv ℝ j (launch V o r g A) 0 v i = iteratedFDeriv ℝ j (L ∘ launch V o r g A) 0 v from
    congrArg (fun T : Panels l [×j]→L[ℝ] G.Color => T v) (L.iteratedFDeriv_comp_left (hq.ready A) (Nat.cast_le.mpr hj)).symm]
  apply le_trans (ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hq.derivatives A p hl h j h₀ hj i) he)
  simp only [Finset.prod_const_one,mul_one]; split; swap; · unfold loom; positivity
  next hi =>
  have he := spine_triangle i.1 o p P.power
  have hh : spine P.power i.1 o ≤ (1+(r:ℝ))^P.power := by rw [spine,separation_comm]; gcongr
  rw [←mul_pow]; unfold loom
  apply (mul_le_mul (le_self_pow₀ hC (by omega : j ≠ 0)) (pow_le_pow_left₀ (mul_pos hp (spine_pos ..)).le (mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_right hh ht.le)) hp.le) j) (pow_nonneg (mul_pos hp (spine_pos ..)).le _) (by positivity)).trans_eq
  rw [←mul_pow]; congr 1; ring
lemma individual {j : ℕ} (hj : j ≤ n) (h₀ : 1 ≤ j) (v : Fin j → Panels l) (he : ∀ a, ‖v a‖ ≤ 1) {b : ℕ} (hb : P.power ≤ b)
    (hh : j=1 ∨ (p=o ∧ P.threshold*(1+(r:ℝ))^P.power ≤ 1)) : Limb b p (iteratedFDeriv ℝ j (launch V o r g A) 0 v) (C*P.threshold) := by
  have hp := P.threshold_pos
  intro i
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond c => G.Color) i
  rw [show iteratedFDeriv ℝ j (launch V o r g A) 0 v i = iteratedFDeriv ℝ j (L ∘ launch V o r g A) 0 v from
    congrArg (fun T : Panels l [×j]→L[ℝ] G.Color => T v) (L.iteratedFDeriv_comp_left (hq.ready A) (Nat.cast_le.mpr hj)).symm]
  apply le_trans (ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hq.derivatives A p hl h j h₀ hj i) he)
  simp only [Finset.prod_const_one,mul_one]; split; swap; · have := spine_pos b i.1 p; positivity
  next hi =>
  rw [mul_assoc]; gcongr ?_*?_
  apply le_trans (b:=P.threshold*spine P.power i.1 p) ?_ (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp) hb) hp.le)
  rcases hh with hh | ⟨rfl,hh⟩; · rw [hh,pow_one]
  apply pow_le_of_le_one (mul_pos hp (spine_pos ..)).le _ (by omega); apply le_trans _ hh
  unfold spine; rw [separation_comm]; gcongr

omit h hl in
lemma visible {b : ℕ} (hb : P.power ≤ b) : Limb b o (crop o r g V) (C*P.threshold) := by
  intro i; have hp := P.threshold_pos
  by_cases hi : separation o i.1 ≤ r
  · exact (hq.size i hi).trans (mul_le_mul_of_nonneg_left (by unfold spine; rw [separation_comm]; exact le_self_pow₀ (by simp) (by have := P.power_ge; omega)) (by positivity))
  rw [crop,if_neg hi,norm_zero]; have := spine_pos b i.1 o; positivity
end Canvas
end YM.PhysicalNext.JointLoad.Heir
