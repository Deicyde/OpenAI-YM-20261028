import YM.Extra.MULTISOURCE_TRAJECTORIES.Smooth
/-!
# Real ambient extensions computing the very same Haar block push

Noise weights are strictly positive even on the extension (nonunitary part
irrelevant to the physical law). The branch probabilities live only on actual
fine configurations. Never assert or need continuity of the prediction in U.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Function Set Filter Lattice Wilson RG MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {c f : Side}

lemma smooth_prod {α E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedCommRing A] [NormedAlgebra ℝ A]
    (s : Finset α) (F : α → E → A) (h : ∀ i∈s,ContDiff ℝ ∞ (F i)) : ContDiff ℝ ∞ (fun x => ∏ i∈s,F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact contDiff_const
  | insert i s hi ih => simp only [Finset.prod_insert hi]; exact (h _ (by simp)).mul (ih (fun i hi => h i (by simp [hi])))

def mPrice (G : Gauge) (M : G.Mat) := 1-M.trace.re / G.repDim

lemma price_smooth (G : Gauge) : ContDiff ℝ ∞ (mPrice G) := by
  have he := (Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap.contDiff (n:=∞)
  unfold mPrice; simp_rw [div_eq_mul_inv]; exact contDiff_const.sub ((Complex.reCLM.contDiff.comp he).mul contDiff_const)

variable (S : StepData c f)

def kernel (β : ℝ) (M Q : Field G c) := ∏ b,
    (S.penaltyZ β G)⁻¹ * Real.exp (-β * S.kernel.penalty * mPrice G (M b * star (Q b)))

lemma kernel_pos (β : ℝ) (M Q : Field G c) : 0 < kernel S β M Q :=
  Finset.prod_pos fun _ _ => mul_pos (inv_pos.mpr (S.penaltyZ_pos _)) (Real.exp_pos _)

lemma kernel_smooth (β : ℝ) : ContDiff ℝ ∞ (uncurry (kernel (G:=G) S β)) := by
  refine smooth_prod _ _ fun b _ => ?_
  exact contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul ((price_smooth G).comp
    (((contDiff_apply ℝ _ b).comp contDiff_fst).mul ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp
      ((contDiff_apply ℝ _ b).comp contDiff_snd))))))



variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def term (β : ℝ) (F : Config G f → E) (t : S.Choices) (x : Field G c) (U : Config G f) :=
  (kernel S β x (matrixField (S.prediction U t)) * S.likelihood U t) • F U

def extended (β : ℝ) (F : Config G f → E) (x : Field G c) := ∑ t, ∫ U,term S β F t x U ∂prior G f

private lemma likelihood_range (h : S.patch.Branches S.kernel G) (t : S.Choices) (U : Config G f) :
    S.likelihood U t ∈ Icc 0 1 := ⟨S.likelihood_pos _ _, (Finset.single_le_sum (a:=t)
      (fun i (_ : i∈Finset.univ) => S.likelihood_pos U i) (Finset.mem_univ _)).trans_eq (S.chosen h _)⟩

private abbrev Params (G : Gauge) (c : Side) (E : Type) := Field G c × ℝ × E

private def params (F : Config G f → E) (t : S.Choices) (U : Config G f) : Params G c E :=
  (matrixField (S.prediction U t),S.likelihood U t,F U)

private def limits (G : Gauge) (c : Side) {f} (F : Config G f → E) : Set (Params G c E) :=
    range (matrixField (G:=G) (n:=c)) ×ˢ Icc 0 1 ×ˢ range F

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma params_mem (h : S.patch.Branches S.kernel G) (F : Config G f → E) (t : S.Choices) (U : Config G f) :
    params S F t U ∈ limits G c F := ⟨mem_range_self _, likelihood_range S h t U,mem_range_self _⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma compact_limits {F : Config G f → E} (hF : Continuous F) : IsCompact (limits G c F) :=
    (isCompact_range matrixField_cont).prod (isCompact_Icc.prod (isCompact_range hF))

private lemma params_meas (h : S.patch.Branches S.kernel G) {F : Config G f → E} (hF : Continuous F) (t : S.Choices) :
    AEStronglyMeasurable (params S F t) (prior G f) := by
  exact (matrixField_cont.comp_aestronglyMeasurable (S.prediction_meas h t).aestronglyMeasurable).prodMk
    ((S.likelihood_meas h t).aestronglyMeasurable.prodMk hF.aestronglyMeasurable)

private def integrand (β : ℝ) (p : Field G c × Params G c E) := (kernel S β p.1 p.2.1 * p.2.2.1) • p.2.2.2

omit [FiniteDimensional ℝ E] in
private lemma integrand_smooth (β : ℝ) : ContDiff ℝ ∞ (integrand (G:=G) (E:=E) S β) :=
    (((kernel_smooth S β).comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))).mul
      (contDiff_fst.comp (contDiff_snd.comp contDiff_snd))).smul (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))

lemma extended_smooth (h : S.patch.Branches S.kernel G) {F : Config G f → E} (hF : Continuous F) (β : ℝ) :
    ContDiff ℝ ∞ (extended S β F) := by
  unfold extended; refine ContDiff.sum fun t _ => ?_
  exact integral_smooth (params_meas S h hF t) (compact_limits hF) (params_mem S h F t) (integrand_smooth S β)

omit [FiniteDimensional ℝ E] in
omit [NormedSpace ℝ E] in
private lemma integrable_compact {A B : Type} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]
    [NormedAddCommGroup B] {K : Set B} {g : A → B} {h : B → E} (hc : Continuous h) (hk : IsCompact K)
    (hg : AEStronglyMeasurable g μ) (hm : ∀ a,g a∈K) : Integrable (fun a => h (g a)) μ := by
  obtain ⟨D,hD⟩ := hk.exists_bound_of_continuousOn hc.continuousOn
  exact Integrable.of_bound (hc.comp_aestronglyMeasurable hg) D (Eventually.of_forall fun a => hD _ (hm a))

lemma term_integrable (h : S.patch.Branches S.kernel G) {F : Config G f → E} (hF : Continuous F) (β : ℝ) (x : Field G c) (t : S.Choices) :
    Integrable (term S β F t x) (prior G f) := by
  have hc : Continuous fun p : Params G c E => integrand S β (x,p) :=
      (integrand_smooth S β).continuous.comp (continuous_const.prodMk continuous_id)
  exact integrable_compact (h:=fun p : Params G c E => integrand S β (x,p)) (g:=params S F t) hc (compact_limits hF) (params_meas S h hF t) (params_mem S h _ t)

lemma extended_eq (h : S.patch.Branches S.kernel G) {F : Config G f → E} (hF : Continuous F) (β : ℝ) (x : Field G c) :
    extended S β F x = ∫ a, (∑ t, S.likelihood a t * kernel S β x (matrixField (S.prediction a t))) • F a ∂prior G f := by
  simp_rw [Finset.sum_smul,mul_comm (S.likelihood _ _)]; rw [integral_finsetSum]
  · rfl
  intro t _; exact term_integrable S h hF β x t

lemma extended_push (h : S.patch.Branches S.kernel G) {F : Config G f → E} (hF : Continuous F) (β : ℝ) (U : Config G c) :
    extended S β F (matrixField U) = S.push β F U := by
  rw [extended_eq S h hF]; rfl

lemma extended_real (h : S.patch.Branches S.kernel G) {F : Config G f → ℝ} (hF : Continuous F) (β : ℝ) (x : Field G c) :
    extended S β (fun U => (F U : ℂ)) x = extended S β F x := by
  rw [extended_eq S h (F:=fun U => (F U : ℂ)) (Complex.continuous_ofReal.comp hF), extended_eq S h hF]
  simp only [Complex.real_smul, smul_eq_mul,← Complex.ofReal_mul]
  exact integral_ofReal

lemma extended_pos (h : S.patch.Branches S.kernel G) {F : Config G f → ℝ} (hF : Continuous F) (he : ∀ U,0<F U) (β : ℝ) (x : Field G c) :
    0 < extended S β F x := by
  let g (U : Config G f) := (∑ t, S.likelihood U t * kernel S β x (matrixField (S.prediction U t))) • F U
  have hg (U : Config G f) : 0 < g U := by
    refine mul_pos (Finset.sum_pos' (fun t _ => mul_nonneg (S.likelihood_pos ..) (kernel_pos S ..).le) ?_) (he U)
    have hh : ∃ t, 0 < S.likelihood U t := by
      by_contra! ha
      have hl := Finset.sum_nonpos (s:=Finset.univ) fun t _ => ha t
      rw [S.chosen h] at hl; linarith
    obtain ⟨t,ht⟩ := hh
    exact ⟨t,Finset.mem_univ _,mul_pos ht (kernel_pos S ..)⟩
  have hi : Integrable g (prior G f) := by
    unfold g; simp_rw [Finset.sum_smul,mul_comm (S.likelihood _ _)]
    exact integrable_finsetSum _ (fun t _ => term_integrable S h hF β x t)
  rw [extended_eq S h hF, integral_pos_iff_support_of_nonneg (fun a => (hg a).le) hi,
    show Function.support g = univ from Set.eq_univ_of_forall fun a => (hg a).ne']
  simp

omit [FiniteDimensional ℝ E] in
lemma invariant_push {F : Config G f → E} {β : ℝ} (h : S.IsKernel β G)
    (he : ∀ (x : Config G c) U (t : Site f → G.El), S.density β (gauge t U) (gauge (t ∘ S.ratio.embed) x) = S.density β U x)
    (hF : Continuous F) (hi : GaugeInvariant F) : GaugeInvariant (S.push β F) := by
  intro t V
  let u := t ∘ S.ratio.parent
  let g (U : Config G f) := S.density β U (gauge t V) • F U
  have hg := S.push_slice h (gauge t V) F (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  change Integrable g _ at hg
  have hm := Wilson.prior_gauge u
  have hh := integral_map (μ:=prior G f) (f:=g) hm.aemeasurable (by rw [hm.map_eq]; exact hg.aestronglyMeasurable)
  rw [hm.map_eq] at hh
  change (∫ a, g a ∂prior G f) = _
  rw [hh]; unfold g StepData.push
  have ht : u ∘ S.ratio.embed = t := funext fun i => congrArg t (S.ratio.embed_parent i)
  simp_rw [hi u,← ht,he]
end YM.Extra.Trajectories
