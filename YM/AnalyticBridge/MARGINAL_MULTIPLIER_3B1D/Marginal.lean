import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Force
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Contraction

/-!
Valuation and exact consumption of a local majorant under the *same* cloud,
retaining the quadratic correction, for any injective sublist. Counted rather
than operator norms; Gaussian normalization paired (no ambient dimension loss).
This is a single multiplier estimate, not an independently resampled bound for
a product of components. Nothing multiplies this by the pending factor under
separate expectations.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d.Marginal
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Precision Tree Matrix Next.SectorChange.Schur Next.SectorChange.ResidualPrice
  FiniteMatrix Gaussian SourceBounds Kernel
open MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius RealInnerProductSpace

section projection
-- Adapt the Mathlib `measurePreserving_restrict₂_multivariateGaussian`

-- labelled embeddings and counting-vector presentation.
variable {ι τ : Type} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def project (e : τ ↪ ι) (x : Vec ι) : Vec τ := x ∘ e

def take (e : τ ↪ ι) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ τ := LinearMap.toContinuousLinearMap
  { toFun := fun x => toLp 2 (fun i => x (e i))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
-- paid_projection adapts the Gaussian coordinate marginal proof from Mathlib's measurePreserving_restrict₂_multivariateGaussian (Rémy Degenne and Etienne Marion). Copyright (c) 2026 Rémy Degenne. All rights reserved. Apache-2.0. See NOTICE.
omit [DecidableEq ι] [DecidableEq τ] in
@[fun_prop] lemma continuous_project (e : τ ↪ ι) : Continuous (project e) := continuous_pi fun i => continuous_apply (e i)
lemma paid_projection (e : τ ↪ ι) {C : Gaussian.Table ι} (h : C.PosDef) :
    MeasurePreserving (project e) (cloud C) (cloud (C.submatrix e e)) := by
  let T := take e
  have H : MeasurePreserving T (multivariateGaussian 0 C) (multivariateGaussian 0 (C.submatrix e e)) := by
    refine ⟨T.continuous.measurable, IsGaussian.ext ?_ ?_⟩
    · simp only [id_eq, integral_id_multivariateGaussian]; rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id, integral_id_multivariateGaussian,map_zero]
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun τ ℝ).toBasis (fun i j => ?_)
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov,covariance_map]
    · have he (i : τ) : (fun u => ⟪(EuclideanSpace.basisFun τ ℝ).toBasis i, u⟫) ∘ T = fun u => u (e i) := by funext u; simp [T,take, PiLp.inner_apply]
      simp_rw [he,covariance_eval_multivariateGaussian h.posSemidef,covarianceBilin_multivariateGaussian ((h.submatrix e.injective).posSemidef)]
      simp
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    exact IsGaussian.memLp_two_id
  let E : EuclideanSpace ℝ ι ≃ᵐ Vec ι := (MeasurableEquiv.toLp 2 _).symm
  have he : MeasurePreserving E.symm (cloud C) (multivariateGaussian 0 C) := MeasurePreserving.symm E (preserving_cloud C)
  exact (preserving_cloud _ |>.comp (H.comp he))

def shrink (v : ℝ) (x : Vec τ) := Real.exp (-v*sumSq x)
def refund (τ : Type) [Fintype τ] (v : ℝ) := (Real.sqrt (Real.pi/v)) ^ Fintype.card τ
lemma shrink_eq (v : ℝ) (x : Vec τ) : shrink v x = ∏ i, Real.exp (-v*(x i)^2) := by simp only [shrink,sumSq,Finset.mul_sum,Real.exp_sum]
lemma shrink_pos (v : ℝ) (x : Vec τ) : 0 < shrink v x := Real.exp_pos _
@[fun_prop] lemma shrink_cont (v : ℝ) : Continuous (shrink v (τ:=τ)) := by unfold shrink sumSq; fun_prop


lemma integrate_shrink {v : ℝ} (hv : 0<v) : Integrable (shrink v (τ:=τ)) ∧ ∫ z : Vec τ,shrink v z = refund τ v := by
  simp_rw [funext (shrink_eq v : ∀ z : Vec τ, _)]
  refine ⟨Integrable.fintype_prod (μ:=fun _ => volume) fun _ => integrable_exp_neg_mul_sq hv,?_⟩
  change (∫ x, ∏ i : τ,Real.exp (-v*(x i)^2) ∂Measure.pi (fun _ : τ => volume)) = _
  rw [MeasureTheory.integral_fintype_prod_eq_prod (f:=fun (_ : τ) (x:ℝ) => Real.exp (-v*x^2))]; simp only [integral_gaussian,Finset.prod_const,Finset.card_univ,refund]

def allowance (C : Gaussian.Table τ) (v a : ℝ) (x : Vec τ) := Real.sqrt C.det * Real.exp (force C x/2) * a * shrink v x

@[fun_prop] lemma allowance_cont (C : Gaussian.Table τ) (v a : ℝ) : Continuous (allowance C v a) := by unfold allowance force dotProduct mulVec; unfold dotProduct; fun_prop

lemma consume (e : τ ↪ ι) {C : Gaussian.Table ι} (h : C.PosDef) {v : ℝ} (hv : 0<v) (a : ℝ) :
    let F := allowance (C.submatrix e e) v a ∘ project e
    Integrable F (cloud C) ∧ (∫ x, F x ∂cloud C) = a*refund τ v / Gaussian.dome τ := by
  intro F
  let L := C.submatrix e e; let μ := cloud L; let u := allowance L v a
  have hL : L.PosDef := h.submatrix e.injective
  have H := under_cloud hL (fun x => Real.sqrt L.det * a * shrink v x)
  dsimp only at H
  have he x : Real.exp (force L x / 2) • (Real.sqrt L.det*a*shrink v x) = u x := by rw [smul_eq_mul]; unfold u allowance; ring
  have hi : Integrable u μ := by
    simp_rw [he] at H; exact H.1.mp ((integrate_shrink hv).1.const_mul _)
  have hP := paid_projection e h
  refine ⟨hP.integrable_comp_of_integrable hi,?_⟩
  have ht : (∫ x, F x ∂cloud C) = ∫ x,u x ∂μ := by unfold μ; rw [← hP.map_eq,integral_map hP.measurable.aemeasurable]; rfl; exact hi.1.mono_ac (by rw [hP.map_eq])
  rw [ht]; have h' := H.2
  simp_rw [integral_const_mul,(integrate_shrink hv).2,he,smul_eq_mul,coat] at h'
  have hg := Real.sqrt_pos.mpr hL.det_pos; have hf := dome_pos (ι:=τ)
  rw [eq_div_iff hf.ne']; nlinarith only [h',hg]

lemma purchase {E : Type*} [NormedAddCommGroup E] (e : τ ↪ ι) {C : Gaussian.Table ι} (h : C.PosDef) {v : ℝ} (hv : 0<v)
    {a : ℝ} (f : Vec ι → E) (hf : AEStronglyMeasurable f (cloud C)) (hh : ∀ x, ‖f x‖ ≤ allowance (C.submatrix e e) v a (project e x)) :
    Integrable f (cloud C) ∧ (∫ x, ‖f x‖ ∂cloud C) ≤ a*refund τ v / Gaussian.dome τ := by
  obtain ⟨hi,he⟩ := consume e h hv a; exact ⟨hi.mono' hf (Eventually.of_forall hh),he ▸ integral_mono ((hi.mono' hf (Eventually.of_forall hh)).norm) hi hh⟩
end projection

open scoped Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {R : Rep G f} {Pq : Tube G S} {Z : ChartRatio G} {I J ρ : Type} [Fintype I] [Fintype J] [Fintype ρ] {F : Forest S.ratio} {A : Stores S} {x η K d δ w E : ℝ} {q : Chi} {V : Config G c} {k : S.Choices}
    {P : Location f I J} {L : Leaf G A x F I J ρ} {Y : LinkArray G (Frozen A x F)} {z : Prices G (Active A x F)} {h : Kernel G c I J ρ}
    {s r o b : Finset ℕ} {m ℓ : ℕ → ℝ}

def valuation (G : Gauge) (I J : Type) [Fintype I] [Fintype J] (K p η : ℝ) (s : Finset ℕ) (m : ℕ → ℝ) :=
  -(Fintype.card J:ℝ)*Real.log p + (2⁻¹*Fintype.card ((I⊕J) × G.ColorIndex))*Real.log K + (Fintype.card (I × G.ColorIndex):ℝ)/η + ∑ i∈s,m i

def ticket (G : Gauge) (I J : Type) [Fintype I] [Fintype J] (K p η : ℝ) (s o : Finset ℕ) (m ℓ : ℕ → ℝ) := (∏ i∈o,ℓ i)*Real.exp (valuation G I J K p η s m)

lemma chart_log_nonpos (q : Chi) (hZ : LocalRatio Z) (hd : 0<d) (he : 4*d<Z.radius) (g : ℝ) : h.chartLog q Z d g V ≤ 0 := by
  apply Finset.sum_nonpos; intro i _; rw [← Real.exp_le_one_iff]; exact (gentle_extended hZ q hd he _).2

lemma true_expense (hP : Margins h V η K) (he : L.Binds Pq k R.beta q d Y z V h) (hp : Power Pq x R.beta k A V q d F E)
    (ha : -(∑ i∈r,h.light S P R i V) ≤ ∑ i∈s,m i)
    (hz : LocalRatio Z) (_hK : 1≤K) (hη : 0<η) (hd : 0<d) (hδ : 4*d<Z.radius) :
    Real.exp (h.expense S P R q Z d r V) ≤ allowance (h.cov V) (η/4) (Real.exp (valuation G I J K (spare Z R.beta) η s m)) (h.draw V) := by
  have h₀ := correction_upper hη hP.Q.gap
  have hS : sumSq (h.signal V) ≤ (Fintype.card (I × G.ColorIndex):ℝ) := by
    rw [he.signal]; apply le_trans (Finset.sum_le_sum (g:=fun _ => (1:ℝ)^2) (fun i _ => ?_)) (by simp)
    simpa only [Leaf.paper,Function.comp_apply,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hp.fees Y (L.active i)) 2
  have hx := chart_log_nonpos (h:=h) (V:=V) q hz hd hδ (coupling R.beta)
  have hL := Real.log_le_log hP.H.solvent.det_pos ((le_abs_self _).trans (det_pay hP.H.cols))
  rw [Real.log_pow] at hL
  have ht := Real.sqrt_pos.mpr hP.C.solvent.det_pos
  have hφ : Real.exp ((2:ℝ)⁻¹*Real.log (h.cov V).det) = Real.sqrt (h.cov V).det := by
    nth_rw 1 [← Real.sq_sqrt hP.C.solvent.det_pos.le, Real.log_pow]; convert! Real.exp_log ht using 2; ring
  unfold allowance shrink
  rw [← hφ, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  unfold valuation expense ledger
  linarith only [h₀,hx,hL,ha,div_le_div_of_nonneg_right hS hη.le]
lemma true_value (hP : Margins h V η K) (he : L.Binds Pq k R.beta q d Y z V h) (hp : Power Pq x R.beta k A V q d F E) (hz : LocalRatio Z) (hK : 1≤K) (hη : 0<η) (hd : 0<d) (hδ : 4*d<Z.radius)
    (ha : Authored R δ w m ℓ) (hR : L.Reads R s o b) :
    let r := Leaf.lights s R (Leaf.field Pq F A V k q d R.beta Y z)
    ‖h.multiplier S L.location R q Z d r o V‖ ≤ allowance (h.cov V) (η/4) (ticket G I J K (spare Z R.beta) η s o m ℓ) (h.draw V) := by
  intro r
  have he' : -(∑ i∈r,h.light S L.location R i V) ≤ ∑ i∈s,m i := by
    refine ((neg_le_abs _).trans ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (g:=m) fun i hi => ?_))).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun i _ _ => (ha.E i).1))
    obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hi
    exact (ha.E i).2 _ ((he.health (hR.E i h₁) _).mpr h₂) [] (Nat.zero_le _) (by simp)
  have hD : ‖doors q d (h.stage (coupling R.beta) V)‖ ≤ 1 := by
    unfold doors; rw [norm_prod]; exact (Finset.prod_le_prod (s:=Finset.univ) (fun _ _ => norm_nonneg _) fun _ _ => (Real.norm_of_nonneg (broad_range q _ _).1).trans_le (broad_range q _ _).2).trans_eq (by simp)
  have hE := true_expense hP he hp he' hz hK hη hd hδ
  unfold multiplier; rw [norm_mul,norm_mul,norm_prod,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul ((mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => norm_nonneg _) hD).trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => (ha.K i).2 _)) hE (Real.exp_pos _).le (Finset.prod_nonneg fun i _ => (ha.K i).1)).trans_eq
  unfold allowance ticket; ring
end YM.AnalyticBridge.MarginalMultiplier3b1d.Marginal
