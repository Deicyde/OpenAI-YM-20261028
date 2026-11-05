import YM.TraceExtension.Fock.TimeData

/-! The dyadic zoom operator on shell amplitudes. Kept as ae classes
so we do not make pointwise off-shell regularity assumptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {m n d : ℕ}

def blow (r : ℝ) := fun x:Space3=>r • x
lemma photon_scales (r : ℝ) (hr : 0<r) : MeasurePreserving (blow r) photon ((ENNReal.ofReal (r⁻¹^2)) • photon) := by
    have hm : Measurable (blow r) := continuous_const_smul r |>.measurable
    refine ⟨hm,?_⟩
    have hx := Measure.map_addHaar_smul (volume (α:=Space3)) hr.ne'
    let c := fun x:Space3 => ENNReal.ofReal (2*‖x‖)⁻¹
    have hc : Measurable c := by unfold c; fun_prop
    rw [show Module.finrank ℝ Space3=3 from finrank_euclideanSpace_fin, ← inv_pow, abs_of_pos (by positivity)] at hx
    change Measure.map (blow r) volume= _ at hx
    ext s hs; unfold photon; change Measure.map _ (volume.withDensity c) _=_; rw [map_apply hm hs,Measure.smul_apply]
    have hf := setLIntegral_map (μ:=volume) hs hc hm
    rw [hx,restrict_smul,lintegral_smul_measure] at hf
    rw [withDensity_apply _ hs,withDensity_apply _ (hm hs)]
    have hu (x) : c x = ENNReal.ofReal r * c (blow r x) := by
      unfold c blow; rw [norm_smul,Real.norm_of_nonneg hr.le,← ENNReal.ofReal_mul hr.le]; congr 1
      by_cases h:x=0
      · simp [h]
      field_simp
    calc
       _ = ∫⁻ x in (blow r) ⁻¹' s, ENNReal.ofReal r*c (blow r x) := setLIntegral_congr_fun (hm hs) (fun x _=> hu x)
       _ = _ := by
        rw [lintegral_const_mul, ← hf,smul_eq_mul,smul_eq_mul,← mul_assoc,← ENNReal.ofReal_mul hr.le]
        · rw [show r*r⁻¹^3=r⁻¹^2 by field_simp]
        exact hc.comp hm

def doubling (i : Fin n) (p : Mom n) := update p i (blow 2 (p i))
lemma stretch (i : Fin n) : MeasurePreserving (doubling i) (photons n) (((2:ℝ≥0∞)⁻¹^2) • photons n) := by
    cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      let f : Mom (n+1) ≃ᵐ Space3 × Mom n := MeasurableEquiv.piFinSuccAbove _ i
      have hm : MeasurePreserving f (photons (n+1)) (photon.prod (photons n)) := measurePreserving_piFinSuccAbove _ i
      have hp : MeasurePreserving (blow 2) photon (((2:ℝ≥0∞)⁻¹^2) • photon) := by convert photon_scales 2 (by norm_num) using 2; rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
      have he := hp.prod (MeasurePreserving.id (photons n)); rw [prod_smul_left (2⁻¹^2)] at he
      have hh : f ∘ doubling i = Prod.map (blow 2) id ∘ f := by
          ext1 p; apply Prod.ext
          · change doubling i p i = _; unfold doubling; rw [update_self]; rfl
          ext1 j; change doubling i p (i.succAbove j) = _; unfold doubling; rw [update_of_ne (i.succAbove_ne j)]; rfl
      have hg : MeasurePreserving f (((2:ℝ≥0∞)⁻¹^2) • photons (n+1)) (((2:ℝ≥0∞)⁻¹^2) • photon.prod (photons n)) := ⟨hm.measurable,by rw [Measure.map_smul, hm.map_eq]⟩
      have hu := hg.symm.comp (he.comp hm)
      rw [← hh,show (f.symm ∘ f ∘ doubling i) = doubling i from funext (fun p=> f.symm_apply_apply _)] at hu; exact hu
lemma stretch_q (i : Fin n) : QuasiMeasurePreserving (doubling i) (photons n) (photons n) :=
    ⟨(stretch i).measurable,by rw [(stretch i).map_eq]; exact fun s h => by rw [Measure.smul_apply,h,smul_zero]⟩

def zoom (i : Fin n) : Module.End ℝ (Wave n) where
    toFun q := q.compQuasiMeasurePreserving _ (stretch_q i)
    map_add' x y := by
        apply AEEqFun.ext
        filter_upwards [AEEqFun.coeFn_compQuasiMeasurePreserving (x+y) (stretch_q i),
          AEEqFun.coeFn_add (x.compQuasiMeasurePreserving _ (stretch_q i)) (y.compQuasiMeasurePreserving _ (stretch_q i)),
          AEEqFun.coeFn_compQuasiMeasurePreserving x (stretch_q i),AEEqFun.coeFn_compQuasiMeasurePreserving y (stretch_q i), (stretch_q i).ae (AEEqFun.coeFn_add x y)] with k ha hb hc hd he
        rw [ha,hb,comp_apply,he,Pi.add_apply,Pi.add_apply,hc,hd]; rfl
    map_smul' t x := by
        apply AEEqFun.ext
        filter_upwards [AEEqFun.coeFn_compQuasiMeasurePreserving (t • x) (stretch_q i), AEEqFun.coeFn_compQuasiMeasurePreserving x (stretch_q i),AEEqFun.coeFn_smul t (x.compQuasiMeasurePreserving _ (stretch_q i)), (stretch_q i).ae (AEEqFun.coeFn_smul t x)] with k ha hb hc hd
        rw [ha,RingHom.id_apply,hc,comp_apply,hd,Pi.smul_apply,Pi.smul_apply,hb]; rfl
lemma zoom_ae (i : Fin n) (q : Wave n) : ⇑(zoom i q)=ᵐ[photons n] q ∘ doubling i := AEEqFun.coeFn_compQuasiMeasurePreserving q (stretch_q i)

private lemma shield_double (i : Fin n) (k : Mom n) : shield d (doubling i k) ≤ 2^d*shield d k := by
    let A (k:Mom n) := ∏ j∈Finset.univ.erase i, env d (k j)
    have he : A (doubling i k)=A k := Finset.prod_congr rfl fun j hj=> by simp only [doubling,update_of_ne (Finset.ne_of_mem_erase hj)]
    have hh (k) : shield d k=env d (k i)*A k := (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
    rw [hh,hh,he,doubling,update_self,← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun j hj=> (env_positive ..).le))
    unfold env blow; rw [← mul_pow,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
lemma tempered_zoom (q : Wave n) (h : tempered q d) (i : Fin n) : tempered (zoom i q) d := by
    unfold tempered at *
    apply (((h.smul_measure (by finiteness : (2:ℝ≥0∞)⁻¹^2≠⊤)).comp_measurePreserving (stretch i)).const_mul ((2:ℂ)^d)).mono
    · apply Measurable.aestronglyMeasurable ((by fun_prop : Measurable fun j : Mom n=> (↑(shield d j)⁻¹:ℂ)).mul (wave_meas _))
    filter_upwards [zoom_ae i q] with j hj
    rw [hj]; simp only [comp_apply,norm_mul, norm_pow];
    have hp := shield_pos d j; have hg := shield_pos d (doubling i j)
    rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simp [Real.norm_of_nonneg hp.le, Real.norm_of_nonneg hg.le]
    have ht := @shield_double n d i j; field_simp; linarith
lemma tempered_sub (p q : Wave n) (h : tempered p d) (hh : tempered q d) : tempered (p-q) d := by
    apply (h.sub hh).ae_eq
    filter_upwards [AEEqFun.coeFn_sub p q] with x hx
    simp only [hx,Pi.sub_apply,mul_sub]
lemma tempered_mul (q : Wave n) (h : tempered q d) (c : ℝ) : tempered (c • q) d := by
    apply (h.const_mul (c:ℂ)).ae_eq
    filter_upwards [AEEqFun.coeFn_smul c q] with i hi; rw [hi]; simp [Complex.real_smul,mul_left_comm]
lemma different (i j : Fin n) : Commute (zoom i) (zoom j) := by
    by_cases hk : i=j
    · rw [hk]
    ext q
    filter_upwards [zoom_ae i (zoom j q), zoom_ae j (zoom i q), (stretch_q i).ae (zoom_ae j q), (stretch_q j).ae (zoom_ae i q)] with x h h' u u'
    change zoom i (zoom j q) x=zoom j (zoom i q) x
    rw [h,h',comp_apply,comp_apply,u,u',comp_apply,comp_apply]; unfold doubling
    rw [update_of_ne (Ne.symm hk),update_of_ne hk,update_comm hk]
end YM.TraceExtension.Photons
