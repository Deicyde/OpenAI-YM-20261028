import YM.RG08.Ward.Evergreen
import Mathlib.Analysis.Calculus.ImplicitContDiff
/-!
# Analytic centered square normal mode

Relative Gram root. Fixed period: coefficients at the actual factorial
conventions may use arbitrarily poor constants in a germ identification.
Doesn't call any uniform∈phase comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter Function Matrix
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators
section square
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "M" => Matrix ι ι ℝ

lemma turnS {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {F : W×(M)→(M)}
    (h : ContDiffAt ℝ ω F (0,1)) (hh : ((fderiv ℝ F (0,1)).comp (ContinuousLinearMap.inr ℝ W (M))).IsInvertible) : ∃ v : W→(M),
      v 0=1 ∧ ContDiffAt ℝ ω v 0 ∧ (∀ᶠ z in 𝓝 0,F (z,v z)=F (0,1)) ∧ ∀ᶠ y in 𝓝 (0,1), F y=F (0,1) ↔ v y.1=y.2 :=
  ⟨h.implicitFunction (by simp) hh,h.implicitFunction_apply_self .., ContDiffAt.contDiffAt_implicitFunction h (by simp) hh, h.eventually_apply_implicitFunction .., h.eventually_apply_eq_iff_implicitFunction ..⟩

lemma turn_square : HasFDerivAt (fun v : M => v*v) ((2:ℝ) • ContinuousLinearMap.id ℝ (M)) 1 := by
  have H:= (hasFDerivAt_id (𝕜:=ℝ) (1:M)).mul' (hasFDerivAt_id (𝕜:=ℝ) (1:M))
  convert! H using 1
  ext v; simp [two_smul]
  rfl

lemma turn_up {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {H : W→(M)}
    (h : ContDiffAt ℝ ω H 0) (hv : H 0=1) : ∃ v : W→(M),v 0=1 ∧ ContDiffAt ℝ ω v 0 ∧ (∀ᶠ y in 𝓝 0,v y*v y=H y) ∧
      ∀ t : W→(M), Tendsto t (𝓝 0) (𝓝 1) → (∀ᶠ y in 𝓝 0,t y*t y=H y) → v=ᶠ[𝓝 0]t := by
  let k (u : W×(M)):= u.2*u.2 - H u.1
  have hk : ContDiffAt ℝ ω k (0,1) := (contDiffAt_snd.mul contDiffAt_snd).sub (h.comp (f:=Prod.fst) _ contDiffAt_fst)
  let P : M → W × (M) := fun x=> (0,x)
  have ht : ((2:ℝ) • ContinuousLinearMap.id ℝ (M)) = (fderiv ℝ k (0,1)).comp (ContinuousLinearMap.inr ℝ W (M)) := by
    have hp : HasFDerivAt P (ContinuousLinearMap.inr ℝ W (M)) 1 := (ContinuousLinearMap.inr ℝ W (M)).hasFDerivAt
    exact ((turn_square (ι:=ι)).sub_const (H 0)).unique ((hk.differentiableAt (by simp)).hasFDerivAt.comp (f:=P) _ hp)
  obtain ⟨v,h1,h2,h3,h4⟩:= turnS hk (by rw [← ht]; exact ⟨(Units.mk0 (2:ℝ) (by norm_num)) • ContinuousLinearEquiv.refl ℝ (M),rfl⟩)
  refine ⟨v,h1,h2,h3.mono (fun i hi=> ?_),fun t hi hx=>?_⟩
  · simpa [k,hv,sub_eq_zero] using hi
  filter_upwards [hx,(tendsto_id.prodMk_nhds hi).eventually h4] with i hi ht
  apply ht.mp
  simp [k,hi,hv]

-- Normal modes for a symmetric analytic path. Needn't be uniform or a
-- designated Hessian square root over the whole period envelope.
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma cont_kinInv {H : E → (M)} (h : ContDiffAt ℝ ω H 0) (he : (H 0).det ≠ 0) : ContDiffAt ℝ ω (fun i => (H i)⁻¹) 0 := by
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  refine ContDiffAt.comp (g:=Ring.inverse) _ ?_ h
  obtain ⟨v,hv⟩:= (Matrix.isUnit_iff_isUnit_det (H 0)).2 (Ne.isUnit he)
  rw [← hv]; exact contDiffAt_ringInverse ℝ _
lemma cont_kinDet {H : E → (M)} (h : ContDiffAt ℝ ω H 0) : ContDiffAt ℝ ω (fun i => (H i).det) 0 := by
  -- scalar component
  simp_rw [Matrix.det_apply]
  refine ContDiffAt.sum fun i _=>?_
  simp only [Units.smul_def, zsmul_eq_mul]
  refine ContDiffAt.mul contDiffAt_const (contDiffAt_prod fun a _=> ?_)
  exact (((Matrix.entryLinearMap ℝ ℝ (i a) a).toContinuousLinearMap).contDiff.contDiffAt.comp _ h)
lemma planets [CompleteSpace E] {H : E→(M)} (h : ContDiffAt ℝ ω H 0) (he : (H 0).det ≠ 0)
    (hp : ∀ᶠ v in 𝓝 0, (H v).IsSymm) : ∃ L : E→(M),L 0=1 ∧ ContDiffAt ℝ ω L 0 ∧
        ∀ᶠ v in 𝓝 0, 0 < (L v).det ∧ (L v)ᵀ*H v*L v=H 0 := by
  let A:=H 0; let B (p:E):= (H p)⁻¹*A
  have hA : B 0=1 := Matrix.nonsing_inv_mul _ (Ne.isUnit he)
  obtain ⟨L,h1,h2,h3,h4⟩:=turn_up (H:=B) ((cont_kinInv h he).mul contDiffAt_const) hA
  let J (p:E) := (H p)⁻¹*(L p)ᵀ*(H p)
  have hx : ∀ᶠ v in 𝓝 0, IsUnit (H v).det := ((cont_kinDet h).continuousAt.eventually_ne he).mono fun _ h=>h.isUnit
  have hz : J 0=1:= by unfold J; rw [h1,transpose_one,_root_.mul_one]; exact hA
  have hy : ContinuousAt J 0:= by
    exact ((cont_kinInv h he|>.continuousAt).mul ((continuous_id.matrix_transpose.continuousAt).comp h2.continuousAt)).mul h.continuousAt
  have hv : ∀ᶠ p in 𝓝 0,J p*J p=B p := by
    filter_upwards [hp,hx,h3] with p hb ht hv
    let X:=H p; let v:= L p; have ht':X*X⁻¹=1:=Matrix.mul_nonsing_inv _ ht; change v*v = X⁻¹*A at hv
    change X⁻¹*vᵀ*X*(X⁻¹*vᵀ*X)=_
    rw [show X⁻¹*vᵀ*X*(X⁻¹*vᵀ*X)=X⁻¹*(vᵀ*(X*X⁻¹)*vᵀ)*X by simp only [_root_.mul_assoc],ht',_root_.mul_one,← transpose_mul,hv,transpose_mul,show Aᵀ=A from hp.self_of_nhds,transpose_nonsing_inv,show Xᵀ=X from hb]
    rw [show X⁻¹*(A*X⁻¹)*X=X⁻¹*A*(X⁻¹*X) by simp only [_root_.mul_assoc], X.nonsing_inv_mul ht, _root_.mul_one]
  refine ⟨L,h1,h2,?_⟩
  filter_upwards [hx,hp,h4 J (hz ▸ hy.tendsto) hv,h3,(cont_kinDet h2|>.continuousAt).eventually (lt_mem_nhds (show 0<(L 0).det by rw [h1,Matrix.det_one]; norm_num))] with p ha Hb HL hU ht
  refine ⟨ht,?_⟩
  calc
    _ = H p * L p * L p := by
        change L p=J p at HL
        have H' : H p*L p=(L p)ᵀ*H p := by
          conv_lhs=>rhs; rw [HL]
          simp only [J,← _root_.mul_assoc,Matrix.mul_nonsing_inv _ ha,_root_.one_mul]
        rw [H']
    _ = _ := by rw [_root_.mul_assoc,show L p*L p=(H p)⁻¹*A from hU,← _root_.mul_assoc,Matrix.mul_nonsing_inv _ ha,_root_.one_mul]
end square
end YM.RG08.Canon
