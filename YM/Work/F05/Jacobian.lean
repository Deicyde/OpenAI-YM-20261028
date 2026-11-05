import YM.Work.F05.Measure
import YM.Work.F05.Reindex


/-!
# Additive Jacobian compared to the physical Haar chart ratios

Use compact measurable tests near each point of interest, freezing the
coarse coordinate. Products live on a common additive space (coordinate
permutation); the two pushforwards live on the actual two forest slices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F05
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Exterior Tree Metric
open scoped Topology ENNReal BigOperators ContDiff Matrix.Norms.Frobenius

private lemma detects {E : Type} [MetricSpace E] [MeasureSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)]
    [Measure.IsOpenPosMeasure (volume : Measure E)] [ProperSpace E] {x : E} {s : Set E}
    {F H : E → ℝ} (hs : s ∈ 𝓝 x) (he : ∀ C : Set E, IsCompact C → C ⊆ s →
      (∫⁻ y in C, ENNReal.ofReal (F y)) = ∫⁻ y in C, ENNReal.ofReal (H y))
    (hF : ContinuousAt F x) (hH : ContinuousAt H x) (hp : 0 ≤ F x) : H x ≤ F x := by
  by_contra! hn
  obtain ⟨a,ha,hb⟩ := exists_between hn
  obtain ⟨b,hab,hb'⟩ := exists_between hb
  have hN : ∀ᶠ y in 𝓝 x, y∈s ∧ F y < a ∧ b < H y :=
    (show ∀ᶠ y in 𝓝 x, y∈s from hs).and ((hF.eventually (gt_mem_nhds ha)).and (hH.eventually (lt_mem_nhds hb')))
  obtain ⟨d,hd,h⟩ := nhds_basis_closedBall.mem_iff.mp hN
  let C := closedBall x d
  have hu (y : E) (hy : y ∈ C) : y∈s ∧ F y < a ∧ b < H y := h hy
  have hv : IsCompact C := isCompact_closedBall x d
  have hw : 0 < volume C := lt_of_lt_of_le
    (isOpen_ball.measure_pos volume ⟨x,mem_ball_self hd⟩) (measure_mono ball_subset_closedBall)
  refine (he C hv (fun y hy => (hu y hy).1)).not_lt ?_
  calc
    _ ≤ ∫⁻ (_ : E) in C, ENNReal.ofReal a := setLIntegral_mono' hv.measurableSet (fun y hy =>
          ENNReal.ofReal_le_ofReal (hu y hy).2.1.le)
    _ < ∫⁻ (_ : E) in C, ENNReal.ofReal b := by
          simp only [lintegral_const, Measure.restrict_apply_univ]
          exact ENNReal.mul_lt_mul_left hw.ne' hv.measure_lt_top.ne
            ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hp.trans ha.le)).mpr hab)
    _ ≤ _ := setLIntegral_mono' hv.measurableSet (fun y hy =>
          ENNReal.ofReal_le_ofReal (hu y hy).2.2.le)

variable {c f : Side} {G : Gauge} {g : Ratio c f} {B T : Forest g}
    {P : ChartRatio G} (e : B.Free ≃ T.Free)

-- Conditions used for compact testing at fixed x
private def gate (P : ChartRatio G) (e : B.Free ≃ T.Free) (x : Bid.Dir G c) (y : AxisChart G B) : Prop :=
  y ∈ parcel B P ∧ index e (move e x y) ∈ parcel T P ∧
  exposure T x (index e (move e x y)) = Profiles.reroute B T G (exposure B x y) ∧
  ContDiffAt ℝ ω (move e x) y

private lemma cost_compact (h : LocalRatio P) (x : Bid.Dir G c)
    (C : Set (AxisChart G B)) (hC : IsCompact C) (hs : C ⊆ {y | gate P e x y}) :
    (∫⁻ y in C, ENNReal.ofReal (load B P y)) =
      ∫⁻ y in C, ENNReal.ofReal (|(fderiv ℝ (move e x) y).det| * load T P (index e (move e x y))) := by
  let F := exposure B x
  let H := exposure T x
  let L : AxisChart G B ≃L[ℝ] AxisChart G T := index e
  let R := move e x
  let f := Profiles.reroute B T G
  let V := R '' C
  let A := L '' V
  have ht (y : AxisChart G B) (hy : y ∈ C) : gate P e x y := hs hy
  have hd (y : AxisChart G B) (hy : y ∈ C) : HasFDerivAt R (fderiv ℝ R y) y :=
    ((ht y hy).2.2.2.differentiableAt (by simp)).hasFDerivAt
  have hw (y : AxisChart G B) (hy : y ∈ C) : H (L (R y)) = f (F y) := (ht y hy).2.2.1
  have hi : InjOn R C := fun a ha b hb e => exposure_inj B h x (ht a ha).1 (ht b hb).1
    (f.injective ((hw a ha).symm.trans ((congr_arg (fun s => H (L s)) e).trans (hw b hb))))
  have hV : IsCompact V := hC.image_of_continuousOn
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
  have hA : IsCompact A := hV.image L.continuous
  have HH : Continuous H := (exposure_continuous T).comp (f:= fun y => (x,y))
    (continuous_const.prodMk continuous_id)
  have he : H '' A = f '' (F '' C) := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨_, ⟨_,⟨w,hw',rfl⟩,rfl⟩,rfl⟩
      rw [hw w hw']; exact mem_image_of_mem _ (mem_image_of_mem _ hw')
    rintro _ ⟨_,⟨w,hw',rfl⟩,rfl⟩
    rw [← hw w hw']; exact mem_image_of_mem _ (mem_image_of_mem _ (mem_image_of_mem _ hw'))
  have hM : (B.order G) (F '' C) = (T.order G) (H '' A) := by
    have hu := (Profiles.spending B T G).measure_preimage
      ((hA.image HH).measurableSet.nullMeasurableSet (μ:=T.order G))
    rw [show f ⁻¹' (H '' A) = F '' C by rw [he, f.injective.preimage_image]] at hu
    exact hu
  have ha : A ⊆ parcel T P := by
    rintro _ ⟨_,⟨w,hw',rfl⟩,rfl⟩; exact (ht w hw').2.1
  have hy : MeasurableEmbedding L := (MeasurableEquiv.piCongrLeft (fun _ => G.Color) e).measurableEmbedding
  calc
    _ = (B.order G) (F '' C) := (order_exposed B h x C hC (fun y hx => (ht y hx).1)).symm
    _ = (T.order G) (H '' A) := hM
    _ = ∫⁻ y in A, ENNReal.ofReal (load T P y) := order_exposed T h x A hA ha
    _ = ∫⁻ y in V, ENNReal.ofReal (load T P (L y)) := by
          have hm : L ⁻¹' A = V := L.injective.preimage_image _
          rw [← hm]
          exact ((index_preserves e).setLIntegral_comp_preimage_emb hy _ _).symm
    _ = ∫⁻ y in C, ENNReal.ofReal |(fderiv ℝ R y).det| * ENNReal.ofReal (load T P (L (R y))) :=
          lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hC.measurableSet
            (fun y hy => (hd y hy).hasFDerivWithinAt) hi _
    _ = _ := by simp only [ENNReal.ofReal_mul (abs_nonneg _)]; rfl

private lemma gate_cost (h : LocalRatio P) (x : Bid.Dir G c) (y : AxisChart G B)
    (hs : ∀ᶠ w in 𝓝 y, gate P e x w) :
    toll B P y = |(fderiv ℝ (move e x) y).det| * toll T P (switch B T x y) := by
  let s := {w | gate P e x w}
  have hy : gate P e x y := hs.self_of_nhds
  let R := move e x
  let L : AxisChart G B ≃L[ℝ] AxisChart G T := index e
  let F (z : AxisChart G B) := load B P z
  let H (z : AxisChart G B) := |(fderiv ℝ R z).det| * load T P (L (R z))
  have hr : ContDiffAt ℝ ω R y := hy.2.2.2
  have hc : ContinuousAt F y := load_cont B h hy.1
  have hd : ContinuousAt (fun z => (fderiv ℝ R z).det) y :=
    ContinuousLinearMap.continuous_det.continuousAt.comp (hr.fderiv_right (m:=ω) (by simp)).continuousAt
  have hu : ContinuousAt H y := hd.abs.mul ((load_cont T h hy.2.1).comp
    (f:= fun z => L (R z)) (L.continuousAt.comp hr.continuousAt))
  have hp : 0 ≤ F y := (load_pos B h hy.1).le
  have hq : 0 ≤ H y := mul_nonneg (abs_nonneg _) (load_pos T h hy.2.1).le
  have he : F y = H y := le_antisymm
    (detects (s:=s) hs (fun C hc hx => (cost_compact e h x C hc hx).symm) hu hc hq)
    (detects (s:=s) hs (cost_compact e h x) hc hu hp)
  unfold F H at he
  rw [load_eq, load_eq, ← free_card B T,
    show L (R y) = switch B T x y from (congr_fun (move_eq e x) y).symm, mul_left_comm] at he
  exact mul_left_cancel₀ (pow_ne_zero _ h.scale.ne') he

lemma toll_switch (h : LocalRatio P) :
    ∀ᶠ z : Bid.Dir G c × AxisChart G B in 𝓝 0,
      toll B P z.2 = |(fderiv ℝ (move e z.1) z.2).det| * toll T P (switch B T z.1 z.2) := by
  have hs : ∀ᶠ z : Bid.Dir G c × AxisChart G B in 𝓝 0, gate P e z.1 z.2 := by
    have hi := (switch_jet B T (G:=G)).continuousAt.tendsto
    change Tendsto (uncurry (switch B T (G:=G))) (𝓝 0) (𝓝 (switch B T (G:=G) 0 0)) at hi
    rw [switch_zero] at hi
    filter_upwards [hi.eventually (parcel_zero T h),
      (continuous_snd.tendsto (0:Bid.Dir G c × AxisChart G B)).eventually (parcel_zero B h),
      exposure_switch B T, (move_jet e).eventually (by simp)] with ⟨x,y⟩ hv hw he hd
    have he' : index e (move e x y) = switch B T x y := (congr_fun (move_eq e x) y).symm
    exact ⟨hw, he'.symm ▸ hv, he'.symm ▸ he, hold_jet hd⟩
  filter_upwards [eventually_eventually_nhds.mpr hs] with ⟨x,y⟩ hx
  exact gate_cost e h x y (hold_near hx)
end YM.Work.F05
