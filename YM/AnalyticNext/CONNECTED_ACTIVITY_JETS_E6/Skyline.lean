import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Many

/-!
# Probability reference on full space

Verify Haar constants inclusively (period-independent reference choice,
empty types). Use unfurled Pi construction and actual sweep. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Poll
open Filter Function MeasureTheory ProbabilityTheory Matrix WithLp
open scoped Topology InnerProductSpace MatrixOrder ContDiff BigOperators ENNReal
variable {ι : Type} [Fintype ι]

theorem map_density {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (e : α≃ᵐβ)
    (μ : Measure α) {d : α→ENNReal} (hd : Measurable d) :
    (μ.withDensity d).map e = (μ.map e).withDensity (d ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),withDensity_apply _ hs,
    setLIntegral_map hs (hd.comp e.symm.measurable) e.measurable]
  simp

theorem uniform_pdf {α : Type} [MeasurableSpace α] (μ : ι→Measure α) [∀ i,SigmaFinite (μ i)]
    (d : ι→α→ℝ) (hd : ∀ i x, 0≤ d i x) (hg : ∀ i,Integrable (d i) (μ i)) :
    Measure.pi (fun i=> (μ i).withDensity (fun x=> ENNReal.ofReal (d i x)))=
      (Measure.pi μ).withDensity (fun y=> ENNReal.ofReal (∏ i, d i (y i))) := by
  let f (y : ι→α) := ∏ i, d i (y i)
  have he := Integrable.fintype_prod hg
  refine Measure.pi_eq fun s h => ?_
  let X := Set.univ.pi s
  have hX : MeasurableSet X := MeasurableSet.univ_pi h
  have hy : ∀ y,0 ≤ f y := fun _=> Finset.prod_nonneg fun i _=>hd i _
  have hx := ofReal_integral_eq_lintegral_ofReal (μ:=(Measure.pi μ).restrict X) he.restrict (ae_of_all _ hy)
  rw [withDensity_apply _ hX,← hx]; unfold X at *
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod d,ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _; rw [withDensity_apply _ (h i)]
    exact ofReal_integral_eq_lintegral_ofReal (hg i).restrict (ae_of_all _ (hd i))
  intro i _; exact integral_nonneg (hd i)

private def std (x : Body ι) := ((Real.sqrt (2*Real.pi))^Fintype.card ι)⁻¹*Real.exp (-‖x‖^2/2)

theorem std_pdf : stdGaussian (Body ι) =
    (volume:Measure (Body ι)).withDensity (fun x=> ENNReal.ofReal (((Real.sqrt (2*Real.pi))^Fintype.card ι)⁻¹*Real.exp (-‖x‖^2/2))) := by
  rw [← map_pi_eq_stdGaussian,gaussianReal_of_var_ne_zero _ (one_ne_zero)]
  change Measure.map _ (Measure.pi (fun _ : ι=> volume.withDensity (fun x=>ENNReal.ofReal (gaussianPDFReal 0 1 x))))=_
  rw [uniform_pdf _ (fun _ : ι=> gaussianPDFReal 0 1) (fun _ _ => gaussianPDFReal_nonneg ..) (fun _ => integrable_gaussianPDFReal ..)]
  let e:= MeasurableEquiv.toLp 2 (ι→ℝ)
  change Measure.map e _ = _
  rw [map_density]; rotate_left
  · fun_prop
  have he : (Measure.pi (fun _:ι=>volume)).map e=(volume : Measure (Body ι)) :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm.map_eq
  rw [he]; congr 1; funext x
  change ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))=_
  apply congr_arg
  simp only [gaussianPDFReal,NNReal.coe_one, mul_one,sub_zero]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,← inv_pow,← Real.exp_sum,← Finset.sum_div]
  simp only [Finset.sum_neg_distrib,EuclideanSpace.real_norm_sq_eq]

variable [DecidableEq ι]

private lemma squared_space {S R : Matrix ι ι ℝ} (hR : R.PosSemidef) (h : R * R=S) (hs : IsUnit S.det)
    (u : Body ι) :
    let A:= toEuclideanCLM (𝕜:=ℝ) R
    dotProduct (ofLp (A u)) (S⁻¹ *ᵥ ofLp (A u))=‖u‖^2 := by
  intro B
  have he : R * S⁻¹ * R=1 := by
    have hg : IsUnit R.det := isUnit_of_mul_isUnit_left (y:=R.det) (by rw [←det_mul,h]; exact hs)
    have hf : R * S⁻¹=R⁻¹ := by
      calc
        _=(R⁻¹*(R*R))*S⁻¹ := by rw [←mul_assoc _ R R, nonsing_inv_mul _ hg,one_mul]
        _=_ := by rw [h,mul_assoc,mul_nonsing_inv _ hs,mul_one]
    rw [hf, nonsing_inv_mul _ hg]
  have hb : ContinuousLinearMap.adjoint B=B := IsSelfAdjoint.adjoint_eq
    ((show IsSelfAdjoint R from hR.nonneg.isSelfAdjoint).map _)
  let C := toEuclideanCLM (𝕜:=ℝ) S⁻¹
  have hh : B*C*B=1 := by dsimp only [B,C]; rw [← map_mul,← map_mul,he,map_one]
  rw [← inner_toEuclideanCLM]; change inner ℝ (B u) (C (B u))=_
  nth_rw 1 [← hb]; rw [ContinuousLinearMap.adjoint_inner_left,← mul_apply_eq_comp,
    ← mul_apply_eq_comp (B * C) B]
  rw [hh]; exact real_inner_self_eq_norm_sq u

/-- Density precisely wrt chosen oriented full Air, no `card!` or boundary
power. -/
theorem sweep_pdf {S : Matrix ι ι ℝ} (hS : S.PosDef) : sweep S =
    volume.withDensity (fun x : Body ι=> ENNReal.ofReal (((Real.sqrt (2*Real.pi))^Fintype.card ι)⁻¹ * Real.exp
      (-Real.log S.det/2-dotProduct (ofLp x) (S⁻¹ *ᵥ ofLp x)/2))) := by
  let R := CFC.sqrt S
  have h : R*R=S := CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg
  have hR : R.PosSemidef := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)
  have hp : 0<S.det := hS.det_pos
  have hd : R.det*R.det=S.det := by rw [←det_mul,h]
  have hr : 0<R.det := by nlinarith only [hR.det_nonneg,hp,hd]
  let A:= toEuclideanCLM (𝕜:=ℝ) R; let B:=toEuclideanCLM (𝕜:=ℝ) R⁻¹
  have ha : A*B=1 := by dsimp only [A,B]; rw [←map_mul,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hr.ne'),map_one]
  have hb : B*A=1 := by dsimp only [A,B]; rw [←map_mul,nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hr.ne'),map_one]
  let e' := ContinuousLinearEquiv.equivOfInverse' A B ha hb
  let e := e'.toHomeomorph.toMeasurableEquiv
  unfold sweep multivariateGaussian; simp_rw [zero_add]; rw [std_pdf]; change Measure.map e _ = _
  let P := volume (α:=Body ι)
  rw [map_density e]; rotate_left
  · fun_prop
  have hl : LinearMap.det (A : Body ι →ₗ[ℝ] Body ι)=R.det := by
    unfold A; rw [coe_toEuclideanCLM_eq_toEuclideanLin,toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]
  have hA := Measure.map_linearMap_addHaar_eq_smul_addHaar P (f:=A.toLinearMap)
    (show LinearMap.det (A.toLinearMap)≠0 by rw [hl]; exact hr.ne')
  have hh : Measure.map e P=ENNReal.ofReal |R.det⁻¹| • P := hl ▸ hA
  rw [hh, abs_of_pos (inv_pos.mpr hr),withDensity_smul_measure, ← withDensity_smul' _ _ (by simp)]
  congr 1; funext x
  change ENNReal.ofReal R.det⁻¹*ENNReal.ofReal (std (e.symm x)) = _
  rw [← ENNReal.ofReal_mul (by positivity)]; apply congr_arg
  have hx := squared_space hR h (isUnit_iff_ne_zero.mpr hp.ne') (e.symm x)
  change dotProduct (ofLp (e (e.symm x))) _=_ at hx
  have hΔ : A (e.symm x)=x := e.apply_symm_apply x
  unfold std; rw [e.apply_symm_apply,hΔ] at hx
  rw [hx,← hd,Real.log_mul hr.ne' hr.ne',Real.exp_sub]; simp_rw [neg_div]
  rw [show -( (Real.log R.det + Real.log R.det)/2)=-Real.log R.det by ring]
  rw [Real.exp_neg,Real.exp_neg,Real.exp_log hr]; ring
end YM.ConnectedActivityE6.Poll
