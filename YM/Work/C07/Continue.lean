import YM.Work.C07.Integrate


/-!
# Continue the compact-tested identity to z=1

On K the test support, do single-complex-variable analytic continuation IN THE SCALING
PARAMETER. The permissible domain is open (compact p) and already convex; no need for
continuation through a seam at a tie. To pass analyticity through integration on K we can
work with `C(K,ℂ)` using weak holomorphy detected by point evaluations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C07
open Boundary Set Filter Function Table Analysis Complex MeasureTheory Bid Mink
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {L : Register G} {S T : Table L} {V : DiffPlan S} {h : S.RealSpin}
    {Y : Waves S} {R : Rotation S} {n : ℕ}

-- work generally with a compact subset K of integration variables
attribute [local instance] Measure.Subtype.measureSpace in
theorem analytic_integral {K : Set (Points n)} (hK : IsCompact K) (B : ℂ → Points n → ℂ)
    {U : Set ℂ} (hU : IsOpen U) (hc : ContinuousOn (uncurry B) (U ×ˢ K))
    (hp : ∀ p ∈ K, DifferentiableOn ℂ (fun z => B z p) U) :
    AnalyticOnNhd ℂ (fun z => ∫ p in K, B z p) U := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : IsFiniteMeasure (volume : Measure K) :=
    ⟨by rw [Measure.Subtype.volume_univ hK.isClosed.measurableSet.nullMeasurableSet]
        exact hK.measure_lt_top⟩
  let D (z : ℂ) := ContinuousMap.mkD (K.restrict (B z)) (0 : C(K,ℂ))
  have he (z) (hz : z ∈ U) : ContinuousOn (B z) K :=
    hc.comp (Continuous.prodMk_right z).continuousOn fun _ hw => ⟨hz, hw⟩
  have hD (z) (hz : z ∈ U) (p : K) : D z p = B z p := by
    dsimp only [D]
    rw [ContinuousMap.mkD_of_continuousOn (he z hz)]; rfl
  let P (p : K) := (ContinuousMap.evalCLM ℂ p : C(K,ℂ) →L[ℂ] ℂ)
  have hF : AnalyticOnNhd ℂ D U := by
    apply lift_weak (Set.range P) (fun f g h => ContinuousMap.ext fun i => h (P i) (mem_range_self i)) hU
      (ContinuousMap.continuousOn_mkD_restrict_of_uncurry B 0 hc)
    rintro _ ⟨x,rfl⟩
    exact (hp x x.2).congr (fun z hz => hD z hz x)
  have hl (f : C(K,ℂ)) : Integrable f :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let A : C(K,ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ p, f p
      map_add' := fun f g => integral_add (hl f) (hl g)
      map_smul' := fun a f => integral_smul a (fun p => f p) }
  let E := LinearMap.mkContinuous A ((volume : Measure K).real univ) (fun f => by
    rw [mul_comm]
    exact norm_integral_le_of_norm_le_const (ae_of_all _ fun p => f.norm_coe_le_norm p))
  intro z hz
  apply ((E.analyticAt _).comp (hF z hz)).congr
  filter_upwards [hU.mem_nhds hz] with w hw
  change (∫ p : K, D w p) = _
  simp_rw [hD w hw]; exact integral_subtype hK.isClosed.measurableSet _

private def allowed (K : Set (Points n)) (y : Heights n) : Set ℂ :=
    {z | ∀ p ∈ K, scaledTimes y z p ∈ strict n}

private lemma scaled_cont (y : Heights n) :
    Continuous (uncurry (scaledTimes y)) := by
  change Continuous fun p : ℂ × Points n => scaledTimes y p.1 p.2
  unfold scaledTimes; fun_prop

private lemma allowed_open {K : Set (Points n)} (y : Heights n) (hK : IsCompact K) : IsOpen (allowed K y) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let W := uncurry (scaledTimes y) ⁻¹' strict n
  have hW : ({z} : Set ℂ) ×ˢ K ⊆ W := by
    rintro ⟨p,q⟩ ⟨hp,hq⟩
    exact (show p=z from hp).symm ▸ hz q hq
  obtain ⟨t,s,ht,-,htz,hsK,H⟩ := generalized_tube_lemma isCompact_singleton hK
    ((open_strict n).preimage (scaled_cont y)) hW
  exact ⟨t, fun a ha b hb => H (mk_mem_prod ha (hsK hb)), ht, htz (mem_singleton z)⟩

private lemma allowed_convex (K : Set (Points n)) (y : Heights n) : Convex ℝ (allowed K y) := by
  rw [convex_iff_forall_pos]
  intro z hz r hr a b ha hb hab p hp i j hij
  have he (k : Fin n) : (scaledTimes y (a • z + b • r) p k).im =
      a * (scaledTimes y z p k).im + b * (scaledTimes y r p k).im := by
    simp only [scaledTimes, add_im, mul_im, ofReal_re, ofReal_im, real_smul,
      I_re, I_im, mul_zero, zero_mul, zero_add, add_zero, mul_one]
    linear_combination -(y k)*hab
  change (scaledTimes y _ p i).im < (scaledTimes y _ p j).im
  rw [he, he]
  exact add_lt_add (mul_lt_mul_of_pos_left (hz p hp hij) ha) (mul_lt_mul_of_pos_left (hr p hp hij) hb)

private lemma allowed_real (K : Set (Points n)) {y : Heights n} (hy : y ∈ east n) (z : ℝ) :
    (z : ℂ) ∈ allowed K y := fun p _ i j h => by simpa [scaledTimes] using hy h

private lemma error_analytic (hr : Y.Region T) (R : Rotation S) {K : Set (Points n)} (hK : IsCompact K)
    (a : SpaceAxis) (y : Heights n) (v : Fin n → S.Tag) (f : Joint n) :
    AnalyticOnNhd ℂ (fun z => ∫ p in K, errorTerm Y R a y v f z p) (allowed K y) := by
  let U := allowed K y
  apply analytic_integral hK _ (allowed_open y hK)
  · have ht : Continuous (fun p : Points n => trace p) := by unfold trace; fun_prop
    have hu (q : Fin n → S.Union) : ContinuousOn (fun p : ℂ × Points n => seen Y q y p.1 p.2)
        (U ×ˢ K) :=
      (hr.together n q).comp ((scaled_cont y).prodMk (ht.comp continuous_snd)).continuousOn
        (by rintro ⟨z,p⟩ ⟨hz,hp⟩; exact ⟨hz p hp, mem_univ _⟩)
    change ContinuousOn (fun p : ℂ × Points n => errorTerm _ _ _ _ _ _ p.1 p.2) _
    have hF : Continuous (fun p : ℂ × Points n => testField a y p.1 f p.2) := by
      unfold testField; refine continuous_finsetSum _ fun i _ => ?_
      have ht (b : Axis) : Continuous (fun p : ℂ × Points n => realTerm i b f p.2) :=
        (realTerm i b f).continuous.comp continuous_snd
      have hi : Continuous (fun p : ℂ × Points n => scaledTimes y p.1 p.2 i) :=
        (continuous_apply i).comp (scaled_cont y)
      exact Continuous.add ((by fun_prop : Continuous fun p : ℂ × Points n => ((p.2 i a.castSucc:ℝ):ℂ)).mul (ht timeAxis))
        ((continuous_fst.mul hi).mul (ht a.castSucc))
    unfold errorTerm
    exact ((hu _).mul hF.continuousOn).sub ((continuous_fst.continuousOn.mul
      (continuousOn_finsetSum _ fun i _ => hu (update (ink v) i (kick R a (v i))))).mul
      (f.continuous.comp continuous_snd).continuousOn)
  intro p hp
  have hk : Differentiable ℂ (fun z => scaledTimes y z p) := by
    unfold scaledTimes; fun_prop
  have hs (q : Fin n → S.Union) : DifferentiableOn ℂ (fun z => seen Y q y z p) U :=
    (hr.hol n q (trace p)).comp hk.differentiableOn fun _ hz => hz p hp
  have hT : Differentiable ℂ (fun z => testField a y z f p) := by
    unfold testField; unfold scaledTimes; fun_prop
  unfold errorTerm
  apply DifferentiableOn.sub ((hs _).mul hT.differentiableOn)
  exact (differentiableOn_id.mul (DifferentiableOn.fun_sum fun i _ => hs
    (update (ink v) i (kick R a (v i))))).mul_const _

private theorem error_one (hO : R.Oriented T) (hR : R.Laws V h) (hS : T.Smooth)
    (hr : Y.Region T) (a : SpaceAxis) (y : Heights n) (hy : y ∈ east n)
    (v : Fin n → S.Tag) (f : Joint n) (hK : HasCompactSupport ⇑f) :
    (∫ p in tsupport f, errorTerm Y R a y v f 1 p) = 0 := by
  let K := tsupport f
  let U := allowed K y
  have h₀ : (0 : ℂ) ∈ U := by simpa using allowed_real K hy 0
  have h₁ : (1 : ℂ) ∈ U := by simpa using allowed_real K hy 1
  apply (error_analytic hr R hK a y v f).eqOn_zero_of_preconnected_of_frequently_eq_zero
    ((allowed_convex K y).isPreconnected) h₀ _ h₁
  intro hh
  have ht : Tendsto (fun w : ℝ => (w : ℂ)*I) (𝓝[>] 0) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Continuous (fun w : ℝ => (w : ℂ)*I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    filter_upwards [self_mem_nhdsWithin] with w hw
    change _ ≠ _; simp [ne_of_gt (show 0<w from hw)]
  have hK' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ U :=
    Eventually.filter_mono nhdsWithin_le_nhds ((allowed_open y hK).mem_nhds h₀)
  obtain ⟨w,hw,hU⟩ := (ht.eventually (hh.and hK')).exists
  exact hw (error_imag hO hR hS hr a y v f w hK hU)

lemma compact_boost (hO : R.Oriented T) (hR : R.Laws V h) (hS : T.Smooth)
    (hr : Y.Region T) (hB : Y.Bounds) (a : SpaceAxis) (y : Heights n) (hy : y ∈ east n)
    (v : Fin n → S.Tag) (f : Joint n) (hK : HasCompactSupport ⇑f) :
    (∑ i, Y.psi (update (ink v) i (kick R a (v i))) y f) = Y.psi (ink v) y (inclined a y f) := by
  have he (p : Points n) (hp : p ∉ tsupport f) : errorTerm Y R a y v f 1 p = 0 := by
    rw [errorTerm, test_zero_off a y _ f hp, image_eq_zero_of_notMem_tsupport hp]
    ring
  let f' := inclined a y f
  let q (i : Fin n) (p : Points n) := seen Y (update (ink v) i (kick R a (v i))) y 1 p * f p
  have hq (q : Fin n → S.Union) (p : Points n) : Y.restricted q y p = seen Y q y 1 p := by rw [seen, scaled_one]; rfl
  have hI (i) : Integrable (q i) := by
    simp_rw [q, ← hq]; apply hB _ _ _ hy
  have hJ : Integrable (fun p => seen Y (ink v) y 1 p * f' p) := by
    simp_rw [← hq]; apply hB _ _ _ hy
  have h₁ := error_one hO hR hS hr a y hy v f hK
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero he] at h₁
  simp_rw [errorTerm, test_one, one_mul, Finset.sum_mul] at h₁
  change (∫ p, seen Y (ink v) y 1 p * f' p - ∑ i, q i p) = 0 at h₁
  rw [integral_sub hJ (integrable_finsetSum _ fun i _ => hI i),sub_eq_zero,
    integral_finsetSum Finset.univ (fun i _ => hI i)] at h₁
  simp_rw [Waves.psi, hq]; exact h₁.symm

end YM.Work.C07
