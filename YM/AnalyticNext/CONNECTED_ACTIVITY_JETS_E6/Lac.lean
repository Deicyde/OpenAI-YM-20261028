import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brush
import YM.Work.B04

/-!
# Nonlinear and linear readings, tangent messages

Target color normalizations then row-analytic test. No dimensional factor
in the pull of a heterogeneous Pi chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Metric Set
open scoped Topology BigOperators ContDiff Classical
variable {E F G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {ι : Type*} {k : ℕ} {d e u v w : ℝ} {f : E→F} {g : F→G} {x : E}

lemma opens (k : ℕ) (h : ContDiffAt ℝ (↑k) f x) (s : Set E) (hs : s∈𝓝 x) : ∃ t, IsOpen t∧ x∈t ∧ t⊆s ∧ ContDiffOn ℝ (↑k) f t := by
  obtain ⟨Z,hZ,hx,h⟩:= _root_.mem_nhds_iff.mp (Filter.inter_mem hs (h.eventually (by simp)))
  exact ⟨Z,hx,h,Set.Subset.trans hZ Set.inter_subset_left,fun i hi => by
    have hh : ContDiffAt ℝ (↑k) f i := (hZ hi).2; exact hh.contDiffWithinAt⟩

lemma linear_pull {f : F→G} (L : E →L[ℝ] F) (h : ContDiffAt ℝ (k:WithTop ℕ∞) f (L x)) :
    iteratedFDeriv ℝ k (f ∘ L) x = (iteratedFDeriv ℝ k f (L x)).compContinuousLinearMap (fun _=> L) := by
  obtain ⟨s,hs,hx,-,hv⟩:= opens _ h univ univ_mem
  have hu : UniqueDiffOn ℝ (L ⁻¹' s) := (hs.preimage L.continuous).uniqueDiffOn
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hu (h.comp _ L.contDiff.contDiffAt) (show x∈(L⁻¹' s) from hx),
    ← iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn h hx]
  exact L.iteratedFDerivWithin_comp_right hv hs.uniqueDiffOn hu hx le_rfl

namespace Brush
variable (p : Brush k u d f x)
lemma reading (L : E →L[ℝ] F) (h : Brush k u d g (L x)) (he : ‖L‖ ≤ e) : Brush k u (d*e) (g ∘ L) x := by
  have hx := h.smooth.comp _ L.contDiff.contDiffAt
  refine ⟨hx,mul_nonneg h.pos ((norm_nonneg _).trans he),fun i hi=>?_⟩
  unfold normJ; rw [linear_pull L (h.smaller hi).smooth]
  apply ((iteratedFDeriv ℝ i g (L x)).norm_compContinuousLinearMap_le _).trans
  rw [mul_pow, ← mul_assoc]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact mul_le_mul (h.order i hi) (pow_le_pow_left₀ (norm_nonneg _) he i) (pow_nonneg (norm_nonneg _) _)
    (mul_nonneg h.nonneg (pow_nonneg h.pos _))
lemma report (p : Brush k u d f x) (L : F →L[ℝ] G) (he : ‖L‖ ≤ v) : Brush k (v*u) d (L ∘ f) x := by
  refine ⟨L.contDiff.contDiffAt.comp _ p.smooth,p.pos,fun i hi=> ?_⟩
  unfold normJ; rw [L.iteratedFDeriv_comp_left (p.smaller hi).smooth le_rfl, mul_assoc]
  exact (L.norm_compContinuousMultilinearMap_le _).trans (mul_le_mul he (p.order i hi) (norm_nonneg _)
    ((norm_nonneg _).trans he))
lemma fold {T : ι → E → F} [Fintype ι] (hd : 0≤d) (hv : 0≤v) (he : ∀ i, Brush k v d (T i) x) :
    Brush k v d (fun w i=> T i w) x := by
  let f x i := T i x
  have hp : ContDiffAt ℝ (↑k) f x := contDiffAt_pi.mpr fun i=> (he i).smooth
  refine ⟨hp,hd,?_⟩; intro i hi
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) ?_
  intro a
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hv (pow_nonneg hd _)) (Finset.prod_nonneg (fun _ _=> norm_nonneg _)))).2 ?_
  intro j
  let L : (ι→F)→L[ℝ]F := ContinuousLinearMap.proj j
  change ‖L _‖≤_
  have hs := L.iteratedFDeriv_comp_left (i:=i) hp (Nat.cast_le.mpr hi)
  have hg : (iteratedFDeriv ℝ i (L ∘ f) x) a= _ := congr_arg (fun T : E[×i]→L[ℝ]F=> T a) hs
  change ‖L (iteratedFDeriv ℝ i f x a)‖≤_
  rw [← show iteratedFDeriv ℝ i (T j) x a=L (iteratedFDeriv ℝ i f x a) from hg]; exact ((iteratedFDeriv ℝ i (T j) x).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right ((he j).order i hi) (by positivity))

lemma pair (h : Brush k u d f x) {g : E→G} (p : Brush k u d g x) : Brush k (u+u) d (fun i => (f i,g i)) x := by
  have hh := h.report (ContinuousLinearMap.inl ℝ F G) (v:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp [Prod.norm_def]))
  have hc := p.report (ContinuousLinearMap.inr ℝ F G) (v:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp [Prod.norm_def]))
  have he := hh.gathering hc; simpa using! he

lemma compound (p : Brush k v 1 g (f x)) (hh : ContDiffAt ℝ (↑k) f x) (hd : 0≤d)
    (he : ∀ i : ℕ,0 < i → i≤k → normJ i f x ≤ d^i) : Brush k (k.factorial*v) d (fun i=> g (f i)) x := by
  have hu : ContDiffAt ℝ (↑k) (g ∘ f) x := p.smooth.comp _ hh
  refine ⟨hu,hd,?_⟩; intro i hi
  obtain ⟨T,hT,hk,-,hf⟩:= opens k p.smooth univ univ_mem
  obtain ⟨Y,hY,hX,hv,hf'⟩:= opens k hh _ (hh.continuousAt (hT.mem_nhds hk))
  change ‖iteratedFDeriv ℝ i (g ∘ f) x‖≤_; rw [← iteratedFDerivWithin_eq_iteratedFDeriv hY.uniqueDiffOn (hu.of_le (Nat.cast_le.mpr hi)) hX]
  apply (norm_iteratedFDerivWithin_comp_le hf hf' (Nat.cast_le.mpr hi) hT.uniqueDiffOn hY.uniqueDiffOn hv hX
    (C:=v) (D:=d) ?_ ?_).trans
  · gcongr; exact p.nonneg
  · intro j hj; rw [iteratedFDerivWithin_eq_iteratedFDeriv hT.uniqueDiffOn (p.smaller (hj.trans hi)).smooth hk]
    simpa only [normJ,one_pow,mul_one] using p.order j (hj.trans hi)
  intro j hp hj; rw [iteratedFDerivWithin_eq_iteratedFDeriv hY.uniqueDiffOn (hh.of_le (by exact_mod_cast hj.trans hi)) hX]
  exact he j hp (hj.trans hi)
end Brush
end YM.ConnectedActivityE6.Blaze
