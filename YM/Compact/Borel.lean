import YM.Compact.State

/-!
# Borel indicators share one projection

Common approx wrt sums of finitely many regular finite measures.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spectral.Rep
open MeasureTheory Measure Filter Set Function Complex
open scoped Topology NNReal ENNReal Real BigOperators InnerProductSpace
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  {H : Hilbert} (A : CC X →⋆ₐ[ℂ] H.Op)

def read (v : H) : CC X →ₗ[ℂ] H := ((ContinuousLinearMap.apply ℂ H.space v).toLinearMap).comp A.toAlgHom.toLinearMap
abbrev L (μ : Measure X) := Lp ℂ 2 μ
abbrev name (μ : Measure X) [IsFiniteMeasure μ] : CC X →L[ℂ] L μ := ContinuousMap.toLp 2 μ ℂ

theorem frame (μ : Measure X) [IsFiniteMeasure μ] [Regular μ] : DenseRange (name μ) := ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num)

theorem weight (v : H) (f : CC X) : ‖read A v f‖=‖name (sees A v) f‖ := by
  let μ := sees A v
  let x := name μ f
  change ‖A f v‖=‖x‖
  suffices he : inner ℂ (A f v) (A f v)=inner ℂ x x by
    rw [@norm_eq_sqrt_re_inner ℂ,@norm_eq_sqrt_re_inner ℂ,he]
  rw [← squares,atState,← pairings,L2.inner_def]; apply integral_congr_ae
  have he : ∀ᵐ a ∂μ, x a=f a := ContinuousMap.coeFn_toLp ..
  filter_upwards [he] with a ha
  change star (f a)*f a=inner ℂ (x a) (x a)
  rw [ha,RCLike.inner_apply]; exact mul_comm _ _

def J (v : H) : L (sees A v) →L[ℂ] H.space := (read A v).extendOfNorm (name _).toLinearMap
lemma reads (v : H) (f : CC X) : J A v (name _ f)=A f v :=
    LinearMap.extendOfNorm_eq (frame _) ⟨1,fun f => show ‖read A v f‖ ≤ _ by rw [weight]; simp⟩ f

lemma iso (v : H) : Isometry (J A v) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  have he := (frame (sees A v)).equalizer ((J A v).continuous.norm)
    (continuous_norm (E := L _)) (g := fun x => ‖J A v x‖) ?_
  · exact congr_fun he x
  funext f
  change ‖J A v (name _ f)‖ = _
  rw [reads]; exact weight ..

lemma pair (v : H) (f g : L (sees A v)) : inner ℂ (J A v f) (J A v g)=inner ℂ f g :=
  LinearIsometry.inner_map_map (show L (sees A v) →ₗᵢ[ℂ] H from
    { (J A v).toLinearMap with norm_map' := fun i => (iso A v).norm_map_of_map_zero (map_zero _) i }) f g

def blob (μ : Measure X) [IsFiniteMeasure μ] {s : Set X} (h : MeasurableSet s) : L μ :=
    indicatorConstLp 2 h (measure_ne_top μ s) 1
omit [TopologicalSpace X] [T2Space X] [BorelSpace X] [CompactSpace X] in
lemma slice {s t : Set X} (h : MeasurableSet s) (ht : MeasurableSet t) (μ : Measure X) [IsFiniteMeasure μ] :
    inner ℂ (blob μ h) (blob μ ht) = ↑(μ.real (s∩t)) := by
  rw [blob,L2.inner_indicatorConstLp_one]; unfold blob
  rw [integral_congr_ae (ae_restrict_of_ae indicatorConstLp_coeFn), integral_indicator ht, restrict_restrict ht]; simp [inter_comm]

def R (v : H) {s : Set X} (h : MeasurableSet s) := J A v (blob (sees A v) h)

lemma everyone (v : H) : R A v (@MeasurableSet.univ X _)=v := by
  unfold R
  rw [show blob (sees A v) MeasurableSet.univ=name (sees A v) 1 from by
    apply Lp.ext; apply EventuallyEq.trans indicatorConstLp_coeFn
    rw [Set.indicator_univ]; exact (ContinuousMap.coeFn_toLp (sees A v) (𝕜 := ℂ) (1 : CC X)).symm,reads,map_one]; rfl

lemma R_norm (v : H) {s} (h : MeasurableSet s) : ‖R A v h‖≤‖v‖ := by
  have he : ‖R A v h‖^2=(sees A v).real s := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), R,pair,slice h h, inter_self];rfl
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [he,← size A v]
  exact measureReal_mono (subset_univ _)

lemma shoots {s} (h : MeasurableSet s) (μ : Measure X) [IsFiniteMeasure μ] [Regular μ] : ∃ f : ℕ → CC X,
    ∀ v : H, sees A v ≤ μ → Tendsto (fun n => A (f n) v) atTop (𝓝 (R A v h)) := by
  obtain ⟨w,hw,hW⟩ := mem_closure_iff_seq_limit.mp (frame μ (blob μ h))
  choose f hf using hw
  have hf := hW.congr' (Eventually.of_forall fun i => (hf i).symm)
  refine ⟨f,fun v hv => ?_⟩
  simp_rw [← reads A v]
  refine (J A v).continuous.continuousAt.tendsto.comp (f := fun i => name _ (f i)) ?_
  apply EMetric.tendsto_nhds.mpr
  intro ε he
  let B (μ : Measure X) [IsFiniteMeasure μ] n := edist (name μ (f n)) (blob μ h)
  have hb (μ : Measure X) [IsFiniteMeasure μ] n :
      B μ n=eLpNorm ((f n:X→ℂ) - s.indicator fun _ => 1) 2 μ := by
    unfold B; rw [Lp.edist_def]; apply eLpNorm_congr_ae
    exact (ContinuousMap.coeFn_toLp μ (f n)).sub indicatorConstLp_coeFn
  apply (EMetric.tendsto_nhds.mp hf ε he).mono
  intro n hn
  change B (sees A v) n < ε
  apply lt_of_le_of_lt _ (show B μ n < ε from hn)
  rw [hb,hb]; exact eLpNorm_mono_measure _ hv

def batch {s : Set X} (h : MeasurableSet s) : H.Op := LinearMap.mkContinuous (σ := RingHom.id ℂ) {
    toFun := fun x : H => R A x h
    map_add' := by
      intro x y
      obtain ⟨f,hf⟩ := shoots A h (sees A x + sees A y + sees A (x+y))
      have he := hf (x+y) (Measure.le_add_left le_rfl)
      simp_rw [map_add] at he
      exact tendsto_nhds_unique he ((hf x (Measure.le_add_right (Measure.le_add_right le_rfl))).add (hf y (Measure.le_add_right (Measure.le_add_left le_rfl))))
    map_smul' := by
      intro c x
      obtain ⟨f,hf⟩ := shoots A h (sees A x+sees A (c • x))
      have he := hf (c • x) (Measure.le_add_left le_rfl)
      simp_rw [map_smul] at he
      exact tendsto_nhds_unique he (tendsto_const_nhds.smul (hf x (Measure.le_add_right le_rfl))) } 1 (fun x => show ‖R A x h‖ ≤ 1*‖x‖ by
        rw [one_mul]; exact R_norm A x h)

lemma fact (M N : H.Op) (h : ∀ x, inner ℂ (M x) x= inner ℂ (N x) x) : M=N := by
  apply sub_eq_zero.mp; apply ContinuousLinearMap.coe_injective
  apply (inner_map_self_eq_zero (M-N).toLinearMap).mp
  intro x; change inner ℂ (M x-N x) x=0
  rw [inner_sub_left,h,sub_self]

lemma value (v : H) {s t : Set X} (h : MeasurableSet s) (ht : MeasurableSet t) :
    inner ℂ (batch A h v) (batch A ht v)=↑((sees A v).real (s∩t)) :=
  (pair A v _ _).trans (slice h ht _)
lemma whole : batch A MeasurableSet.univ=ContinuousLinearMap.id ℂ _ := ContinuousLinearMap.ext (fun i => everyone A i)
lemma outer (v : H) {s : Set X} (h : MeasurableSet s) : inner ℂ (batch A h v) v=↑((sees A v).real s) := by
  simpa [whole] using value A v h MeasurableSet.univ
lemma inner' (v : H) {s : Set X} (h : MeasurableSet s) : inner ℂ v (batch A h v)=↑((sees A v).real s) := by
  simpa [inner_conj_symm] using congr_arg (starRingEnd ℂ) (outer A v h)
lemma refl {s : Set X} (h : MeasurableSet s) : (batch A h).adjoint=batch A h := by
  apply fact; intro x; rw [ContinuousLinearMap.adjoint_inner_left,outer, inner']
lemma joins {s t : Set X} (h : MeasurableSet s) (hv : MeasurableSet t) :
    (batch A h).comp (batch A hv) = batch A (h.inter hv) := by
  apply fact; intro x
  rw [outer A _ (h.inter hv), ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_right,refl,value, inter_comm]
lemma nobody : batch A MeasurableSet.empty=0 := by
  ext1 x; change J A x (blob _ _)=0
  rw [blob,indicatorConstLp_empty,map_zero]
end YM.Spectral.Rep
