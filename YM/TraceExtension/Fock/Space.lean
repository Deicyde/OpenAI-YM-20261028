import YM.TraceExtension.LaplaceSchwartz

/-! Wave function conventions in `prop:nfock`. Full direct sum, including vacuum,
finite copies. Ambient L² (impose the symmetric transverse subspace separately).
Use disjoint union to expose conditional wave functions without any slot-domain assumptions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical Interval

/-- Shell-origin assigned zero density as it has zero volume. -/
def photon : Measure Space3 := volume.withDensity fun x : Space3 => ENNReal.ofReal (2 * ‖x‖)⁻¹
instance : NullSingletonClass photon := by unfold photon; infer_instance
instance : SigmaFinite photon := SigmaFinite.withDensity_of_ne_top
    (ae_of_all _ fun _ => ENNReal.ofReal_ne_top)
lemma photon_ball {r : ℝ} (hr : 0<r) : photon (closedBall 0 r) = ENNReal.ofReal (Real.pi*r^2) := by
    let f : ℝ → ℝ := fun x => (2*x)⁻¹
    let U := closedBall (0:Space3) r
    have hi (x:Space3) : 0 ≤ f ‖x‖ := by unfold f; positivity
    have ht : (∫ x in U, f ‖x‖) = Real.pi*r^2 := by
        let g := (Iic r).indicator f
        have he : (∫ x in U, f ‖x‖)=∫ x : Space3,g ‖x‖ := by
             rw [← integral_indicator (f:=fun x => f ‖x‖) measurableSet_closedBall]
             congr! 1; ext x; simp [g, Set.indicator]
        rw [he, integral_fun_norm_addHaar]; rw [show Module.finrank ℝ Space3=3 from finrank_euclideanSpace_fin]
        rw [Measure.real,EuclideanSpace.volume_ball_fin_three]
        have hp : 0 ≤ Real.pi*4/3 := by positivity
        norm_num [ENNReal.toReal_ofReal hp]
        rw [show (fun x:ℝ => x^2 * g x)=(Iic r).indicator (fun x => (2:ℝ)⁻¹*x) by
              ext x; by_cases h:x∈Iic r
              · by_cases ht:x=0
                · simp [g, ht, Set.indicator, hr.le]
                simp only [g,Set.indicator_of_mem h,f]; field_simp
              simp [g,h], setIntegral_indicator measurableSet_Iic,Ioi_inter_Iic,← intervalIntegral.integral_of_le hr.le, intervalIntegral.integral_const_mul, integral_id]
        ring
    rw [← ht]; symm; exact ofReal_integral_eq_lintegral_ofReal (by
        by_contra h; rw [integral_undef h] at ht; exact (by positivity : 0<Real.pi*r^2).ne ht) (ae_of_all _ hi) |>.trans (withDensity_apply _ measurableSet_closedBall).symm
instance photon_growth : photon.HasTemperateGrowth := by
    have he := inverse_integrable (μ:=photon) (A:=Real.pi) (k:=2) Real.pi_pos.le (fun R hr => (photon_ball (zero_lt_one.trans_le hr)).le)
    exact ⟨3,by
        simp_rw [show ∀ p : Space3,(1+‖p‖) ^ (- ((3:ℕ):ℝ))=((1+‖p‖)^3)⁻¹ from fun p => by rw [Real.rpow_neg (by positivity),Real.rpow_natCast] ]
        exact he⟩

/-- Space / time coordinates, forward cone covectors. -/
def momentum (k : Space3) : E4 := position k ‖k‖
@[simp] lemma momentum_energy (k) : time (momentum k) = ‖k‖ := by simp [momentum]
@[simp] lemma momentum_space (k) : spatial (momentum k)= k := by simp [momentum]
@[simp] lemma momentum_zero : momentum 0=0 := ext_by (by simp) (by simp)
@[fun_prop] lemma momentum_cont : Continuous momentum := divide.symm.continuous.comp (continuous_id.prodMk continuous_norm)

abbrev Label (m : ℕ) := Fin m × SpaceAxis -- copy, spatial component
abbrev Tags (m n : ℕ) := Fin n → Label m
abbrev Mom (n : ℕ) := Fin n → Space3
def photons (n : ℕ) : Measure (Mom n) := Measure.pi fun _ => photon
instance (n : ℕ) : SigmaFinite (photons n) := by unfold photons; infer_instance
lemma photons_nonzero (n : ℕ) : ∀ᵐ k ∂photons n, ∀ i, 0 < ‖k i‖ :=
    ae_all_iff.mpr fun i => (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin n => photon) (i:=i)).eventually
      (show ∀ᵐ y : Space3 ∂photon, 0< ‖y‖ from (ae_iff.mpr (by simp)))

/-- sectors, kept as compatible simultaneous ordered colors and momenta -/
abbrev Index (m : ℕ) := Σ n, Tags m n
abbrev Wavespace (m : ℕ) := Σ i : Index m, Mom i.1

variable {m n : ℕ}
def totalMomentum (k : Mom n) := ∑ i, momentum (k i)
@[simp] lemma total_energy (k : Mom n) : time (totalMomentum k)=∑ i, ‖k i‖ := by
    unfold totalMomentum; rw [← clockL_at, _root_.map_sum]; simp
@[fun_prop] lemma total_cont : Continuous (@totalMomentum n) := by unfold totalMomentum; fun_prop
abbrev forward (x : Wavespace m) := totalMomentum x.snd

abbrev insertP (i : Index m) (k : Mom i.1) : Wavespace m := ⟨i,k⟩

private lemma measW {s : Set (Wavespace m)} : MeasurableSet s ↔ ∀ i, MeasurableSet (insertP i ⁻¹' s) := by
    exact MeasurableSpace.measurableSet_iInf
lemma disjointP (i j : Index m) (h : i ≠ j) (s : Set (Mom i.1)) : insertP j ⁻¹' (insertP i '' s) = ∅ := by
    ext k; refine ⟨?_,fun H => False.elim H⟩; rintro ⟨p,_,H⟩; exact False.elim (h (Sigma.mk.inj H).1)
lemma embedP (i : Index m) : MeasurableEmbedding (insertP i) := by
    have he : Injective (insertP i) := fun a b h => eq_of_heq ((Sigma.mk.inj h).2)
    refine ⟨he,fun s hs => measW.mp hs i,fun s hs => measW.mpr fun j => ?_⟩
    by_cases h : i=j
    · subst j; rw [he.preimage_image]; exact hs
    rw [disjointP i j h]; exact MeasurableSet.empty
lemma measurable_sector {V : Type*} [MeasurableSpace V] (f : Wavespace m → V) (h : ∀ i, Measurable (f ∘ insertP i)) : Measurable f :=
    fun _ he => measW.mpr fun i => h i he
lemma measurable_forward : Measurable (@forward m) := measurable_sector _ fun _ => total_cont.measurable

def sumMeasure (m : ℕ) : Measure (Wavespace m) := Measure.sum fun i : Index m => (photons i.fst).map (insertP i)
lemma sum_ae (P : Wavespace m → Prop) : (∀ᵐ k ∂sumMeasure m, P k) ↔ ∀ i, ∀ᵐ k ∂photons i.fst, P (insertP i k) := by
    unfold sumMeasure; rw [Measure.ae_sum_iff]; simp_rw [(embedP _).ae_map_iff]
lemma sum_part (i : Index m) {s : Set (Mom i.fst)} (h : MeasurableSet s) : sumMeasure m (insertP i '' s) = photons i.fst s := by
    rw [sumMeasure,Measure.sum_apply _ ((embedP i).measurableSet_image' h), tsum_eq_single i]
    · rw [(embedP i).map_apply,(embedP i).injective.preimage_image]
    intro j he; rw [(embedP j).map_apply, disjointP _ _ (Ne.symm he),measure_empty]
instance : SigmaFinite (sumMeasure m) := by
    let A (i : Index m × ℕ) := insertP i.1 '' spanningSets (photons i.1.1) i.2
    refine Measure.sigmaFinite_of_countable (countable_range A) (fun s h => ?_) ?_
    · obtain ⟨j,rfl⟩ := h; unfold A; rw [sum_part _ (measurableSet_spanningSets ..)]; exact measure_spanningSets_lt_top ..
    refine Set.eq_univ_of_forall ?_; rintro ⟨k,i⟩
    obtain ⟨j,hj⟩ : ∃ j, i∈spanningSets (photons k.fst) j := mem_iUnion.mp (by rw [iUnion_spanningSets]; trivial)
    exact mem_sUnion.mpr ⟨A (k,j),mem_range_self _,⟨i,hj,rfl⟩⟩

lemma sum_hasSum {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Wavespace m → V) (hf : Integrable f (sumMeasure m)) :
    HasSum (fun i : Index m => ∫ k,f (insertP i k) ∂ photons i.fst) (∫ k,f k ∂ sumMeasure m) := by
    unfold sumMeasure; change Integrable _ (Measure.sum _) at hf
    have hp := hasSum_integral_measure hf; simp_rw [(embedP _).integral_map] at hp; exact hp

/-- Ambient direct integral; use field-identification hypothesis with images transverse and symmetric. -/
abbrev Ambient (m : ℕ) := Lp ℂ 2 (sumMeasure m)
end YM.TraceExtension.Photons
