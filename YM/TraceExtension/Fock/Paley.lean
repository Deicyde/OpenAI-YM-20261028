import YM.TraceExtension.Fock.Annihilate

/-! One-sided frequency uniqueness. We use bounded continuous boundary
versions (after smearing), prove even from vanishing on just an interval
via Gaussian test steepening. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral Paley
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical

variable {F : ℂ → ℂ} {C : ℝ}
private def adjusted (s r : ℝ) (z : ℂ) := (↑(Real.exp ((r*s)^2)):ℂ)*Paley.probe (-2*r^2*s) (r^2) z
private lemma shifted (h : Air F C) (s r : ℝ) (hs : 0≤s) (hr : 0<r) :
    (∫ t : ℝ, F (Z 0 (r⁻¹*t))*adjusted s r (Z 0 (r⁻¹*t))) = ∫ t : ℝ,F (Z s (r⁻¹*t))* (↑(Real.exp (-t^2)):ℂ) := by
    have he (t : ℝ) : adjusted s r (Z s (r⁻¹*t))=(↑(Real.exp (-t^2)):ℂ) := by
        unfold adjusted; rw [probe, ofReal_exp,← Complex.exp_add, ofReal_exp]; congr 1; unfold Z; push_cast; ring_nf; simp only [I_sq]; field_simp [(ofReal_ne_zero.mpr hr.ne')]; ring
    simp_rw [← he];
    have hu (x : ℝ) : (∫ t : ℝ,F (Z x (r⁻¹*t))*adjusted s r (Z x (r⁻¹*t)))=
        (((r⁻¹)^Module.finrank ℝ ℝ):ℝ)⁻¹ • ((↑(Real.exp ((r*s)^2)):ℂ)*(∫ t:ℝ, F (Z x t)*probe (-2*r^2*s) (r^2) (Z x t))) := by
        let f (t : ℝ) := F (Z x t)*adjusted s r (Z x t)
        change (∫ t,f (r⁻¹ • t))=_
        rw [Measure.integral_comp_smul_of_nonneg volume _ _ (hR:=by positivity),← integral_const_mul];
        congr! 1; unfold f adjusted; simp_rw [mul_left_comm (F _)]
    rw [hu,hu,same h s _ _ hs (sq_pos_of_pos hr)]

private lemma half_vanish (h : Air F C) (s : ℝ) (hs : 0<s) (hp : ∀ t : ℝ, |t| < 2*s → F (t:ℂ)=0) : F (Z s 0)=0 := by
    let f r t := F (Z 0 (r⁻¹*t))*adjusted s r (Z 0 (r⁻¹*t)); let b (t:ℝ) := Real.exp (-(1/2)*t^2)
    have he : Tendsto (fun r => ∫ t,f r t) atTop (𝓝 0) := by
        rw [show (0:ℂ) = ∫ _ : ℝ, (0:ℂ) by simp];
        apply tendsto_integral_filter_of_dominated_convergence (fun t => C*b t) (Eventually.of_forall fun r=> ?_) _ ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/2)).const_mul C)
        · apply ae_of_all; intro t; apply tendsto_const_nhds.congr'
          have he := (tendsto_inv_atTop_zero (𝕜:=ℝ)).mul_const t; rw [zero_mul] at he
          filter_upwards [he.abs.eventually (gt_mem_nhds (by rw [abs_zero]; linarith : |(0:ℝ)|<2*s))] with r hr
          unfold f; rw [gap_zero,hp _ hr,zero_mul]
        · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr; filter_upwards with t
          have ht := h.bounded (Z 0 (r⁻¹*t)) (by simp [high]);
          by_cases hx : |r⁻¹*t| < 2*s
          · simp only [f,gap_zero,hp _ hx,zero_mul,norm_zero]; exact mul_nonneg h.rate (Real.exp_nonneg _)
          dsimp only [f,adjusted]; rw [norm_mul]; apply mul_le_mul ht _ (norm_nonneg _) h.rate
          rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _),probed]; unfold b
          simp only [zero_pow (by decide : 2 ≠ 0), mul_zero,add_zero, Real.exp_zero,mul_one,← Real.exp_add,Real.exp_le_exp]
          rw [neg_mul,mul_pow r⁻¹ t, ← mul_assoc (r^2),← mul_pow,mul_inv_cancel₀ hr.ne',one_pow,one_mul]
          rw [not_lt,abs_mul,abs_of_pos (inv_pos.mpr hr),mul_comm r⁻¹,← div_eq_mul_inv,le_div_iff₀ hr] at hx
          nlinarith [sq_abs t, sq_le_sq₀ (show 0 ≤ 2*s*r by positivity) (abs_nonneg t) |>.2 hx]
        exact (show Continuous (f r) from by
           let g := fun t : ℝ => r⁻¹*t; have hg : Continuous g := by unfold g; fun_prop
           exact (((h.cont _ (show 0 ≤ (0:ℝ) from le_rfl))).comp hg).mul (continuous_const.mul ((monitors ..).comp hg))).aestronglyMeasurable
    let c (t:ℝ) := Real.exp (-t^2)
    have hv : Integrable c := by simpa [c] using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
    let L := fun r t => F (Z s (r⁻¹*t)) * (↑(c t):ℂ)
    have hc : Tendsto (fun r : ℝ => ∫ t,L r t) atTop (𝓝 (∫ t:ℝ,F (Z s 0)*(↑(c t):ℂ))) := by
        have hQ : Continuous (fun t => F (Z s t)):= h.cont s hs.le
        apply tendsto_integral_filter_of_dominated_convergence (fun t => C*c t) _ _ (hv.const_mul C)
        · apply ae_of_all; intro t; have he := (tendsto_inv_atTop_zero (𝕜:=ℝ)).mul_const t; rw [zero_mul] at he
          exact ((hQ.tendsto 0).comp he).mul_const _
        · exact Eventually.of_forall fun r => (show Continuous (L r) from (hQ.comp (show Continuous fun t => r⁻¹*t from by fun_prop)).mul
            (Complex.continuous_ofReal.comp (by unfold c; fun_prop))).aestronglyMeasurable
        exact Eventually.of_forall fun r=> ae_of_all _ fun i=> by change ‖_ * (_:ℂ)‖ ≤ _; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ c i from Real.exp_nonneg _)]; gcongr; exact h.bounded _ (by simp [high,hs.le])
    have hy := tendsto_nhds_unique_of_eventuallyEq hc he ((eventually_gt_atTop _).mono fun i hi=> (shifted h s i hs.le hi).symm)
    rw [integral_const_mul,integral_complex_ofReal] at hy
    have hb : (∫ t,c t)=Real.sqrt Real.pi := by simpa [c] using integral_gaussian (1:ℝ)
    rw [hb] at hy; exact (mul_eq_zero.mp hy).resolve_right (Complex.ofReal_ne_zero.mpr (by positivity))

lemma bottom_identity (h : Air F C) (hx : ∀ᶠ r : ℝ in 𝓝 0,F (r : ℂ)=0) (t : ℝ) : F (t:ℂ)=0 := by
    obtain ⟨s,hs,hp⟩ := Metric.eventually_nhds_iff.mp hx
    have hv (u:ℝ) (hu:0<u) (hp':2*u<s) : F (Z u 0)=0 := half_vanish h u hu fun t ht => hp (by simpa [Real.dist_eq] using (lt_trans ht hp'))
    let k := s/4; have hy : 0<k:=by unfold k; positivity
    have he : EqOn F (fun _=>0) loft := by
        refine (h.straight.analyticOnNhd Paley.open_loft).eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
          ((convex_halfSpace_gt imCLM.toLinearMap.isLinear 0).isPreconnected) (show Z k 0 ∈ loft by simp [loft,hy]) ?_
        intro p
        have hm : Tendsto (fun r=> Z r 0) (𝓝[>] k) (𝓝[≠] Z k 0) := by
           apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
           · exact (show Continuous fun r => Z r 0 from by unfold Z; fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
           filter_upwards [self_mem_nhdsWithin] with i hi
           change Z i _≠Z k 0; intro e; exact (show k < i from hi).ne' (by simpa using congr_arg Complex.im e)
        have hc := hm.eventually p
        obtain ⟨i,⟨hI,hh⟩,he⟩ := ((hc.and self_mem_nhdsWithin).and
          ((gt_mem_nhds (show k<s/2 by unfold k; linarith)).filter_mono nhdsWithin_le_nhds)).exists
        change k < i at hh; change i < s/2 at he
        exact hI (hv i (by linarith) (by linarith))
    have hp : Tendsto (fun r => F (Z r t)) (𝓝[>] 0) (𝓝 (F (Z 0 t))) := by
        refine (h.connects (x := Z 0 t) (by simp [high])).tendsto.comp ?_
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun r => Z r t) ((by continuity : Continuous (fun r => Z r t)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        filter_upwards [self_mem_nhdsWithin] with r hr; exact (Paley.subset (show Z r t∈loft from by unfold loft; rw [mem_setOf,level]; exact hr))
    rw [gap_zero] at hp; exact tendsto_nhds_unique_of_eventuallyEq hp tendsto_const_nhds (Eventually.mono self_mem_nhdsWithin (fun r hr => he (show Z r t∈loft from by simpa [loft] using hr)))
end YM.TraceExtension.Photons
