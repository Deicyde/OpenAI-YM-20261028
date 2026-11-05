import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Banjo


set_option warningAsError false

/-! # Expectations replacing one-body lead, Part I: Banjo over a noise fiber

Arithmetic trick: instead of requiring smoothness k+1 to average a
*tensor approximation* over noise, transfer PMOM prices directly at
random endpoints (fits Mute, won't FIT triangular readout). Pay ALL jets
in Promise currency, with a random factor which will be tested only
in moments. Even the highest orders may be charged (no need to extract
non-atomic partitions or compare positions). Use only for small support!
Requires along the radial *random* rays the visited plaques all Health –
additional price later tested by a second-derivative/chord criterion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Quartet
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open Mom Lyre Banjo Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {d : ℕ} {r C M : ℝ} {P : BudgetPoint} {o : Site n} {X : Support n}



/-- assembler to pay even high jets with pure calibrated b and one
 correction Sized at width currency r^(d+1). Coefficient is M,
 can buy this PLUS high derivatives of b in one such correction.
 Can take `b=0` via Promise, which doesn't need X through such steps. -/
lemma sweet {Y : ℝ} (h : 0 ≤ C) (h' : 0 ≤ Y) (he : C+Y ≤ M) (hr : 0 ≤ r) {x y : Directions G n}
    (hx : Promise d C r P o X x) (hy : Sized (Y*r^(d+1)) (y-x) P o) : Promise d M r P o X y := by
  obtain ⟨v,hv,hV,H⟩:=hx
  let u (i : Fin (d+1)) := v i + if i=Fin.last d then y-x else 0
  have hm : C ≤ M := (le_add_of_nonneg_right h').trans he
  refine ⟨u,?_,fun i => ⟨mul_nonneg (h.trans hm) (pow_nonneg hr _), ?_⟩,fun i hi => ?_⟩
  · unfold u; rw [sum_add_distrib]; simp [← hv,add_sub_cancel]
  · unfold u; intro j; by_cases ht : i=Fin.last d
    · subst ht; simp only [if_true, Pi.add_apply, Fin.val_last]; apply (norm_add_le ..).trans
      calc
        _ ≤ (C+Y)*r^(d+1)*width P o j := (add_le_add ((hV (Fin.last d)).2 j) (hy.2 j)).trans_eq (by simp; ring)
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (pow_nonneg hr _)) (width_pos ..).le
    simp only [if_neg ht,add_zero]; refine ((hV i).2 j).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (pow_nonneg hr _)) (width_pos ..).le)
  unfold u; by_cases hx : i=Fin.last d
  · simp [hx] at hi
  simp only [if_neg hx,add_zero]; exact H i hi




end YM.MultiNext.SignedSource.Quartet
namespace YM.MultiNext.SignedSource.Quartet
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open Mom Lyre Banjo Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}




end YM.MultiNext.SignedSource.Quartet
