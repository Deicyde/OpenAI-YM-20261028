import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shutter

/-!
# Neumann at counting estimates. Integrate powers.

True powers iteration prices post-L joint E smallness. All formulas use
few powers, no reliance on spectra log chosen branch. In logs need all
ordered bond walks incl low-radius query when decorating integral as label!
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Pulse
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c : Side} {ι : Type*} {a : ι→Site c} {B : ℕ} [DecidableEq ι] [Fintype ι]
variable {η Q : ℝ} {A : Matrix ι ι ℝ}

lemma raising (h : Price a a A η Q) (hn : 0≤Q) (he : 0≤η) (n : ℕ) : Price a a (A^n) η (Q^n) := by
  induction n with
  | zero => rw [pow_zero,pow_zero]; exact one_pay ..
  | succ i ih => rw [pow_succ,pow_succ]; exact paid_mul ih h he (by positivity) hn

lemma involves (h : Price a a A η Q) (hn : 0≤Q) (he : 0≤η) (hX : Q<1) :
    (IsUnit (1-A).det) ∧ HasSum (fun n : ℕ => A^n) (1-A)⁻¹ := by
  have hx : Summable (fun n : ℕ => A^n) := by
    apply Pi.summable.mpr; intro i; apply Pi.summable.mpr; intro j
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one hn hX) ?_
    intro n; exact only_price (raising h hn he n).1 he i j
  have ht := hx.hasSum
  let S := ∑' n : ℕ, A^n
  have hh : S*(1-A)=1 := by
    apply tendsto_nhds_unique (ht.tendsto_sum_nat.mul_const (1-A))
    have hp (n : ℕ) := _root_.geom_sum_mul_neg A n
    simp_rw [hp]
    simpa only [sub_zero] using (hx.tendsto_atTop_zero.const_sub 1)
  exact ⟨Matrix.isUnit_det_of_left_inverse hh,(Matrix.inv_eq_left_inv hh).symm ▸ ht⟩

lemma stitch {P E : Matrix ι ι ℝ} (h : Price a a E η Q) (hn : 0≤Q) (he : 0≤η) (hX : Q<1)
    (ht : A*P-1=E) : HasSum (fun n : ℕ => P*(-E)^n) A⁻¹ := by
  obtain ⟨ha,hb⟩ := involves (spent_neg h) hn he hX
  have hs : A*(P*(1- -E)⁻¹)=1 := by
    rw [← mul_assoc, show A*P=1- -E by rw [← ht]; abel]
    exact Matrix.mul_nonsing_inv _ ha
  rw [Matrix.inv_eq_right_inv hs]; exact hb.mul_left _

/-- Correct order in C-density inversion. -/
lemma waltz {C E : Matrix ι ι ℝ} (h : Price a a E η Q) (hn : 0 ≤ Q) (he : 0≤η) (hX : Q<1)
    (ht : A*C-1=E) : HasSum (fun n : ℕ => (-E)^n * A) C⁻¹ := by
  obtain ⟨ha,hb⟩ := involves (spent_neg h) hn he hX
  have hs : ((1- -E)⁻¹ * A) * C=1 := by
    rw [mul_assoc, show A*C=1- -E by rw [← ht]; abel]
    exact Matrix.nonsing_inv_mul _ ha
  rw [Matrix.inv_eq_left_inv hs]; exact hb.mul_right _

lemma warp {A C E : Matrix ι ι ℝ} (h : Price a a E η Q) (hn : 0≤Q) (he : 0≤η) (hX : Q<1)
    (ht : A*C-1=E) : HasSum (fun n : ℕ => (-E)^(n+1)*A) (C⁻¹-A) := by
  let F (n : ℕ) := (-E)^n*A
  have hx := waltz h hn he hX ht
  have hh := (summable_nat_add_iff 1).2 hx.summable
  have he : (∑' n : ℕ, F (n+1))=C⁻¹-A := by
    have hf : (∑ i ∈ range 1, F i)+(∑' n : ℕ, F (n+1))=C⁻¹ := (hx.summable.sum_add_tsum_nat_add 1).trans hx.tsum_eq
    rw [sum_range_one,show F 0=A by simp [F]] at hf; rw [← hf]; abel
  rw [← he]; exact hh.hasSum

/-- Use for diagonal endpoint trace, not for unrooted determinant pricing. -/
lemma up_integral {κ : Type*} [Countable κ] (K : κ→ℝ) (hS : Summable K)
    (F : κ → ℝ → ℝ) (h : ∀ x, ContinuousOn (F x) (Set.uIcc (0:ℝ) 1))
    (ht : ∀ x (y : ℝ), y∈Set.Icc (0:ℝ) 1 → |F x y| ≤ K x) (u : ℝ→ℝ)
    (he : ∀ y ∈ Set.Icc (0:ℝ) 1, HasSum (fun x => F x y) (u y)) :
    HasSum (fun x => ∫ y in (0:ℝ)..1, F x y) (∫ y in (0:ℝ)..1,u y) := by
  let U := Set.Ioc (0:ℝ) 1
  let E x := ∫ y in U, ‖F x y‖
  have hx : Summable E := by
    apply Summable.of_nonneg_of_le (fun x => MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun y _ => norm_nonneg _)) _ hS
    intro x
    rw [← intervalIntegral.integral_of_le zero_le_one]
    apply (le_abs_self _).trans
    have hk : ∀ y ∈ Set.uIoc (0:ℝ) 1, ‖‖F x y‖‖ ≤ K x := fun y hy => by
      rw [Set.uIoc_of_le zero_le_one] at hy
      rw [Real.norm_of_nonneg (norm_nonneg _),Real.norm_eq_abs]
      exact ht x y (Set.Ioc_subset_Icc_self hy)
    simpa only [sub_zero,abs_one,mul_one,Real.norm_eq_abs] using! (intervalIntegral.norm_integral_le_of_norm_le_const hk)
  have hh := hasSum_integral_of_summable_integral_norm (F:=F) (μ:= volume.restrict U) (fun x => (h x).intervalIntegrable.1) hx
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  have hw : (∫ (y : ℝ) in U, ∑' x, F x y) = ∫ (y : ℝ) in U, u y := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun y hy => (he _ (Set.Ioc_subset_Icc_self hy)).tsum_eq
  exact hw ▸ hh
end YM.ConnectedActivityE6.Pulse
