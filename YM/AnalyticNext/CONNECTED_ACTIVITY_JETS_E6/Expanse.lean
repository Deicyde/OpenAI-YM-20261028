import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Batch
import YM.Push.ABSOLUTE_SUMS.Copies

/-!
# Repetitions with factorial. Signed/absolute.
Finite at every volume under the crystal. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Letter
open Filter Function Lattice RG Pressure Finset MeasureTheory
open Push Push.AbsoluteSums   Ursell Trees Multiple
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι κ : Type} {w : ι→ℝ}

private lemma columns [Fintype κ] (f : κ→ℕ→ℝ) (z : κ→ℝ) (hf : ∀ i, HasSum (f i) (z i)) : HasSum
    (fun u : κ→ℕ => ∏ i, f i (u i)) (∏ i,z i) := by
  let F (u : κ→ℕ) := ∏ i, f i (u i)
  let μ (i : κ) := Measure.count (α:=ℕ)
  haveI : ∀ i,SigmaFinite (μ i) := fun _=>inferInstanceAs (SigmaFinite (Measure.count (α:=ℕ)))
  have he i : Integrable (f i) (μ i) := integrable_count_iff.mpr (hf i).summable.norm
  have hv : Integrable F (Measure.pi μ) := MeasureTheory.Integrable.fintype_prod he
  have hm : Measure.pi μ=Measure.count := by
    rw [← Measure.sum_smul_dirac (Measure.pi μ), ← Measure.sum_smul_dirac (Measure.count (α:=κ→ℕ))]; unfold μ; simp
  have hz i : ∫ x,f i x ∂μ i=z i := by rw [integral_countable (he i)]; simpa only [μ, measureReal_def, Measure.count_singleton,
    ENNReal.toReal_one,one_smul] using (hf i).tsum_eq
  have hx : (∫ u,F u ∂Measure.pi μ)=∏ i,z i := by unfold F; rw [integral_fintype_prod_eq_prod f]; simp_rw [hz]
  rw [← hx,integral_countable hv]; rw [hm] at hv ⊢; simp_rw [measureReal_def, Measure.count_singleton, ENNReal.toReal_one,one_smul]
  exact (integrable_count_iff.mp hv).of_norm.hasSum

def coins (w : ℝ) (n : ℕ) := w^(n+1)/(n+1).factorial
lemma coins_value (w : ℝ) : HasSum (coins w) (Real.exp w-1) := by
  rw [Real.exp_eq_exp_ℝ]; simpa using! (hasSum_nat_add_iff' 1).2 (NormedSpace.expSeries_div_hasSum_exp w)
lemma coins_row (w : ι → ℝ) (s : Finset ι) : HasSum (fun l => manyW w ⟨s,l⟩) (∏ i∈s,(Real.exp (w i)-1)) := by
  rw [← Finset.prod_coe_sort]
  exact columns (fun i:↥s=> coins (w i.val)) _ (fun _=> coins_value _)

private lemma sharp_cost (x : ℝ) : ‖Real.exp x-1‖ ≤ ‖x‖*Real.exp ‖x‖ := by
  rw [Real.norm_eq_abs,Real.norm_eq_abs]; by_cases h : x<0
  · have hg := Real.add_one_le_exp x; have he : Real.exp x < 1 := Real.exp_lt_one_iff.mpr h
    rw [abs_of_nonpos (by linarith),abs_of_neg h]; apply le_trans _ (le_mul_of_one_le_right (neg_nonneg.mpr h.le)
      (Real.one_le_exp (neg_nonneg.mpr h.le))); linarith
  have hp := le_of_not_gt h; rw [abs_of_nonneg hp,abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hp))]
  have he := Real.add_one_le_exp (-x); rw [Real.exp_neg] at he
  have hx := mul_le_mul_of_nonneg_right he (Real.exp_pos x).le; rw [inv_mul_cancel₀ (Real.exp_ne_zero x)] at hx; linarith
lemma shallow (h : Summable w) : Summable fun i=> Real.exp (w i)-1 := by
  let f i:= ‖w i‖; let C:=∑' i,f i; have hh : Summable f := h.norm
  refine Summable.of_norm_bounded (hh.mul_right (Real.exp C)) fun i=> ?_
  have hx i : f i ≤ C := Summable.le_tsum hh i (fun i _ => norm_nonneg _)
  exact (sharp_cost _).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (hx i)) (norm_nonneg _))
lemma coins_all (h : Summable w) :
    HasSum (fun s : Finset ι=> ∏ i∈s,(Real.exp (w i)-1)) (Real.exp (∑' i,w i)) := by
  let f i:= Real.exp (w i)-1
  let g i:= 1+f i
  have hg i : g i= Real.exp (w i) := by unfold g f; abel
  have h1 : ∀ i,0 < g i := fun i=> (hg i).symm ▸ Real.exp_pos _
  have hx : (fun i=> Real.log (g i))=w := funext fun i=> by rw [hg,Real.log_exp]
  have hy : Summable (fun s : Finset ι=> ∏ i∈s,f i) := by
    have hW := summable_finsetProd_of_summable_nonneg (fun i:ι=> norm_nonneg (f i)) (shallow h).norm
    exact Summable.of_norm_bounded hW fun i=> le_of_eq (norm_prod ..)
  have ht := Real.rexp_tsum_eq_tprod (f:=g) h1 (hx.symm ▸ h); rw [hx] at ht
  have ht' := tprod_one_add hy
  convert! hy.hasSum using 1; exact ht.trans ht'

lemma abs_bill (w : ι → ℝ) (p : Multiple.Reps ι) : ‖manyW w p‖=manyW (fun i=>‖w i‖) p := by unfold manyW; simp only [norm_prod,norm_div,norm_pow]; simp

theorem concert (h : Summable w) : HasSum (manyW w) (Real.exp (∑' i,w i)) := by
  refine (coins_all h).sigma_of_hasSum (coins_row w) (Summable.of_norm ?_)
  simp_rw [abs_bill]; let f i:=‖w i‖
  apply (summable_sigma_of_nonneg (fun i=> manyW_nonneg (fun k=> norm_nonneg (w k)) i)).2
  refine ⟨fun i=> (coins_row f i).summable, ?_⟩
  change Summable (fun x : Finset ι=> ∑' l, manyW f ⟨x,l⟩); simp_rw [(coins_row f _).tsum_eq]; exact (coins_all h.norm).summable
end YM.ConnectedActivityE6.Letter
