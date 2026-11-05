import YM.RG08.Arc.Hall
/-! # Shifted Haar charts with one external path and arbitrary local windows
Measures and normalization explicitly kept. No period-pricing. -/
set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
namespace YM.RG08.Reflect
open Filter Set Metric MeasureTheory YM.PertExtension.Series.Tested
open YM.PertExtension.Series.Radial YM.PertExtension.Chart
open scoped BigOperators Topology Real ContDiff Classical
variable (G : Gauge) (U : Type) [Fintype U]
variable {D : Precision.ChartRatio G}
local notation "E" => U → G.Color
local notation "Z" => (U → G.Color) × ℝ
local notation "T" => tangent G U
local notation "Ω" => physical G U

def plates (x : E) : Z := (x,1)
def hold := (T).map (plates G U)
omit [Fintype U] in
@[fun_prop] lemma plates_meas : Measurable (plates G U) := by unfold plates; fun_prop
instance : (hold G U).HasTemperateGrowth := by
  obtain ⟨n,hn⟩:=Measure.HasTemperateGrowth.exists_integrable (μ:=T)
  refine ⟨n,(integrable_map_measure ?_ (plates_meas ..|>.aemeasurable)).mpr (hn.mono' ?_ (Eventually.of_forall fun i=> ?_))⟩
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · apply Measurable.aestronglyMeasurable
    fun_prop
  change ‖(1+‖plates G U i‖)^(-(n:ℝ))‖≤_
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr; exact norm_fst_le (plates G U i)) (neg_nonpos.mpr (Nat.cast_nonneg _))

lemma gain (b : E) (g : E→ℝ)(t : ℝ)(h : 0≤t) : (t^Module.finrank ℝ (E))⁻¹ * (∫ x,g x∂T)=∫ x,g (t•x+b)∂T := by
  rw [← MeasureTheory.integral_add_right_eq_self g b]
  exact (Measure.integral_comp_smul_of_nonneg T (fun x:E=> g (x+b)) t (hR:=h)).symm
lemma illuminate {F : Z→ℝ} (h : Measurable F) (s : Set Z) (he : MeasurableSet s) :
    (∫ p in s,F p ∂hold G U)=∫ x,s.indicator F (plates G U x) ∂T := by
  rw [← integral_indicator he,hold, integral_map ((plates_meas ..).aemeasurable) ((h.indicator he).aestronglyMeasurable)]

-- windows independent off the layer plate(Dir); clip to estimated disc for all z.
def race (M : ℝ→ E) (r δ : ℝ) (U' : ℝ→Set (U→G.El)) (t : ℝ) : Set Z := disc t δ ∩ {z:Z | (t • z.1+M t)∈ball 0 r ∧ expLinks G U (t • z.1+M t)∈ U' t}

lemma bill_flip {α : Type*} [NormedAddCommGroup α] {f g : ℝ→α} {n : ℕ} (h : Bill n f) (hp : f=ᶠ[𝓝[>] 0]g) : Bill n g := by
  obtain ⟨C,hC,H⟩:=h; exact ⟨C,hC,(hp.and H).mono fun _ ⟨hu,hv⟩=> hu ▸ hv⟩
lemma chambers {ε : ℝ} (h : 0<ε) : chamber G U ε ∈ 𝓝 (1:U→G.El) := by
  obtain ⟨D,hD⟩:=LocalH.actual G; let r:= min (small G D) ε
  have hr:0<r:=lt_min (Ratio.small_pos hD) h
  apply mem_of_superset ((Ratio.chamber_open hD (min_le_left (small G D) ε) (U:=U)).mem_nhds (show (1:U→G.El)∈ _ from fun i _=>⟨0,mem_ball_self hr,G.mat_lieExp_zero⟩))
  exact fun x hx i hi=> image_mono (ball_subset_ball (min_le_right ..)) (hx i hi)
lemma exp_lit {r : ℝ}{x : E} (hr : 0<r)(h : x∈ball 0 r) : expLinks G U x∈ chamber G U r := by
  rw [ball_pi _ hr] at h; exact fun i _ => ⟨x i, h i (by assumption),rfl⟩

private lemma platen {t δ r : ℝ} {x b:E} (ht:0<t) (h : t<δ) (hp:r≤δ/2) (hh:t•x+b∈ball 0 r) (hX : b∈ball 0 (δ/2)) : plates G U x ∈ disc t δ := by
  refine (disc_mem ht.le δ _).2 ?_
  have hz := mem_ball_zero_iff.mp hh; have hD:=mem_ball_zero_iff.mp hX
  rw [plates,Prod.norm_def,mul_max_of_nonneg _ _ ht.le]; refine max_lt ?_ ?_
  · rw [show t*‖x‖=‖t•x‖ by rw [norm_smul,Real.norm_eq_abs, abs_of_pos ht]]
    refine (le_trans (b:=‖t•x+b‖+‖b‖) ?_ le_rfl).trans_lt (by linarith)
    simpa using norm_sub_le (t•x+b) b
  simpa

-- path can be rescaled by any active movement; need just M→0.
-- likelihood can be divided by any scalar path weight w t. no divisions at t=0.
-- conditional follows for ALL sufficiently small open windows; upper in Hausdorff topology expressed via nested sets.
lemma shift_hall (P : Precision.LocalRatio D) (M : ℝ→ E) (hm : Tendsto M (𝓝[>] 0) (𝓝 0))
    (φ : ℝ→ (U → G.El)→ℝ) (w : ℝ→ℝ) (hp : ∀ᶠ t in 𝓝[>] 0,Measurable (φ t))
    (f K : Z→ℝ) (hf : Measurable f) (hK : Measurable K) (hs : Stationary f) (he : ContDiffAt ℝ ∞ K 0)
    (H : ∃ c>0,∀ u:Z,c*‖u‖^2 ≤ jet f 2 u)
    (hx : ∃ a>0, ∀ᶠ t in 𝓝[>] 0, ∀ x:E, (t • x + M t)∈ball 0 a → YM.PertExtension.Series.Radial.projection K f t (plates G U x) =
        w t*(jacobian D (t•x+M t)*φ t (expLinks G U (t•x+M t)))) (n : ℕ) :
    ∃ s ∈ 𝓝 (1:U→G.El), ∀ A : ℝ → Set (U→G.El), (∀ᶠ t in 𝓝[>] 0, MeasurableSet (A t) ∧ A t⊆s) →
      (∃ y ∈ 𝓝 1,∀ᶠ t in 𝓝[>] 0,y⊆A t) →
      Bill (n+1) ((fun t=> w t*((t^Module.finrank ℝ (E))⁻¹*(∫ x in A t, φ t x ∂Ω))) - peval (moment (hold G U) K f) n) := by
  obtain ⟨δ,hδ,hB⟩:=localized (hold G U) he hK hf hs H n
  obtain ⟨a,ha,hY⟩:=hx
  let r:=min (min a (δ/2)) ((small G D)/2)
  have hr : 0<r := lt_min (lt_min ha (half_pos hδ)) (half_pos (Ratio.small_pos P))
  have hl:r≤δ/2 := (min_le_left ..).trans (min_le_right ..)
  have hF:r≤a := (min_le_left ..).trans (min_le_left ..)
  have hz:r<small G D := lt_of_le_of_lt (min_le_right ..) (half_lt_self (Ratio.small_pos P))
  refine ⟨chamber G U r,chambers G U hr,fun A hQ ⟨y,hy,hT⟩=> ?_⟩
  let S := race G U M r δ A
  have hi (t) (h : MeasurableSet (A t)) : MeasurableSet (S t) := (disc_meas ..).inter ((isOpen_ball.measurableSet.preimage (by fun_prop)).inter (h.preimage (expLinks_meas.comp (by fun_prop)))) -- membership
  refine bill_flip (hB δ hδ le_rfl S (hQ.mono fun t ⟨h,_⟩=>⟨hi _ h, inter_subset_left⟩) ?_) ?_
  · have hu : ContinuousAt (expLinks G U) 0 := by
      apply Continuous.continuousAt; apply continuous_pi; intro i; exact G.lieExp_cont.comp (continuous_apply _)
    rw [ContinuousAt,show expLinks G U 0=1 from funext fun _=>G.mat_lieExp_zero] at hu
    obtain ⟨ε,hε,hU⟩:=Metric.mem_nhds_iff.mp (hu hy)
    let z:=min (min (ε/2) (r/2)) δ
    have hw:0<z:=lt_min (lt_min (half_pos hε) (half_pos hr)) hδ
    refine ⟨z,hw,?_⟩
    filter_upwards [hT,hm (Metric.ball_mem_nhds 0 hw)] with t ht hh
    intro x hg
    change x∈disc t δ ∧ _
    have hg' : ‖t•x‖<z:= mem_ball_zero_iff.mp hg
    have hz1:z≤ε/2:=(min_le_left ..).trans (min_le_left ..); have hz2:z≤r/2 := (min_le_left ..).trans (min_le_right ..)
    have ha : ‖t•x.1+M t‖ < z+z := (norm_add_le ..).trans_lt (add_lt_add ((norm_fst_le (t•x)).trans_lt hg') (mem_ball_zero_iff.mp hh))
    have hc : t•x∈ball 0 δ:= (ball_subset_ball (min_le_right (min (ε/2) (r/2)) δ)) (show t•x∈ball 0 z from hg)
    have h₁ : t•x.1+M t∈ball 0 r := mem_ball_zero_iff.mpr (by linarith)
    have h₂ : t•x.1+M t∈ball 0 ε := mem_ball_zero_iff.mpr (by linarith)
    exact ⟨hc,h₁,ht (hU h₂)⟩
  filter_upwards [hY,hQ,eventually_pos,eventually_top hδ,hp, hm (Metric.ball_mem_nhds 0 (half_pos hδ))] with t HT ⟨hL,hX⟩ ht ht' hφ hd
  let X:=A t
  have htL := Ratio.chamber_open P (U:=U) hz.le |>.measurableSet
  have HE : (∫ x in A t, φ t x ∂Ω)=∫ x in ball 0 r, jacobian D x* (X.indicator (φ t) (expLinks G U x)) ∂T := by
    rw [← Ratio.chamber_integral P (X.indicator (φ t)) (hφ.indicator hL) hz hr, integral_indicator hL, Measure.restrict_restrict_of_subset hX]
  rw [Pi.sub_apply,Pi.sub_apply]
  congr 1 -- path; monitor
  change (∫ p in S t,YM.PertExtension.Series.Radial.projection K f t p ∂hold G U)=_
  rw [HE,← integral_indicator (μ:=T) (s:=ball 0 r) isOpen_ball.measurableSet (f:=fun x => jacobian D x * X.indicator (φ t) (expLinks G U x)),gain G U (M t) _ _ ht.le,← integral_const_mul (w t), illuminate G U (projection_meas hK hf ..) (S t) (hi t hL)]
  apply integral_congr_ae; apply Eventually.of_forall
  intro x
  dsimp only
  by_cases hg:t•x+M t∈Metric.ball 0 r
  · have hh' : plates G U x ∈ disc t δ := platen G U ht ht' hl hg hd
    rw [indicator_of_mem hg]
    by_cases hx:expLinks G U (t•x+M t)∈A t
    · rw [indicator_of_mem (s:=X) hx,indicator_of_mem (s:=S t) (show plates G U x∈ S t from ⟨hh',hg,hx⟩)]; exact HT x ((ball_subset_ball hF) hg)
    rw [indicator_of_notMem (s:=X) hx, indicator_of_notMem (s:=S t) (show plates G U x∉ S t from fun h=> hx h.2.2)]; ring
  rw [indicator_of_notMem hg, indicator_of_notMem (s:=S t) (show plates G U x∉ S t from fun h=>hg h.2.1), mul_zero]
end YM.RG08.Reflect
