import YM.Next.FLUCTUATIONS.Charts



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Ratio symmetry and quadratic *error*, for any committed ChartRatio

Evenness follows from price-measure inversion invariance (probability Haar),
not an extra promise of `LocalRatio`, and not assuming the committed `J` is
a particular algorithm for the differential of exp. Give uniform per-link
remainder in a pre-L patch (and thus log-product *extensive* bound). .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric NormedSpace
open scoped Topology ENNReal BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge}

lemma exp_negative (x : G.Color) : G.lieExp (-x) = (G.lieExp x)⁻¹ := by
  apply G.mat_injective
  simp only [G.mat_inv, G.mat_lieExp, map_neg, star_exp, G.colorMat_skew]

/-- For compact tests within the chosen patch, recover even the mass
of the link exponential image (we integrate `Z.scale` also). -/
lemma cap_price {Z : ChartRatio G} (h : LocalRatio Z) (s : Set G.Color) (hs : IsCompact s)
    (hx : s ⊆ ball 0 Z.radius) :
    G.probHaar (G.lieExp '' s) = ∫⁻ y in s, ENNReal.ofReal (Z.scale * Z.J y) := by
  have he := (hs.image G.lieExp_cont).measurableSet
  let U := G.lieExp '' ball 0 Z.radius
  have ht : G.probHaar (G.lieExp '' s) = G.probHaar.restrict U (G.lieExp '' s) := by
    rw [Measure.restrict_apply he, inter_eq_left.mpr (image_mono hx)]
  rw [ht, ← h.actual, Measure.map_apply G.lieExp_cont.measurable he,
    withDensity_apply _ (G.lieExp_cont.measurable he),Measure.restrict_restrict (G.lieExp_cont.measurable he)]
  have hp : G.lieExp ⁻¹' (G.lieExp '' s) ∩ ball 0 Z.radius = s := by
    ext x; refine ⟨?_,fun he => ⟨mem_image_of_mem _ he,hx he⟩⟩
    rintro ⟨⟨z,hz,hi⟩,hd⟩
    exact h.inject (hx hz) hd hi ▸ hz
  rw [hp]

lemma opposite_cap {Z : ChartRatio G} (h : LocalRatio Z) (s : Set G.Color) (hs : IsCompact s)
    (hx : s ⊆ ball 0 Z.radius) :
    (∫⁻ y in s, ENNReal.ofReal (Z.scale*Z.J y)) =
      ∫⁻ y in s, ENNReal.ofReal (Z.scale*Z.J (-y)) := by
  let n := fun y : G.Color => -y
  let t := n '' s
  have ht : IsCompact t := hs.image continuous_neg
  have hl : t ⊆ ball 0 Z.radius := by
    rintro _ ⟨x,hx',rfl⟩; simpa [n] using hx hx'
  have hn : MeasurePreserving n volume volume := (LinearIsometryEquiv.neg ℝ (E:=G.Color)).measurePreserving
  have hp := hn.setLIntegral_comp_emb
    measurableEmbedding_neg (fun y => ENNReal.ofReal (Z.scale*Z.J y)) s
  change (∫⁻ y in s, ENNReal.ofReal (Z.scale*Z.J (-y))) = ∫⁻ y in t, ENNReal.ofReal (Z.scale*Z.J y) at hp
  rw [hp, ← cap_price h _ hs hx, ← cap_price h t ht hl]
  have hw : G.lieExp '' t = Inv.inv ⁻¹' (G.lieExp '' s) := by
    ext x; constructor
    · rintro ⟨_, ⟨z,hz,rfl⟩,rfl⟩
      refine ⟨z,hz,?_⟩
      simp [n,exp_negative]
    rintro ⟨z,hz,he⟩
    exact ⟨n z, mem_image_of_mem _ hz, by simp [n,exp_negative,he]⟩
  rw [hw, G.preserve_inv.measure_preimage (hs.image G.lieExp_cont).measurableSet.nullMeasurableSet]

/-- As in F05 determinant comparison, continuity upgrades compact-set
tests to each point with an open chart buffer. -/
lemma price_le_of_caps {E : Type} [MetricSpace E] [ProperSpace E] [MeasureSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] [Measure.IsOpenPosMeasure (volume : Measure E)]
    {x : E} {s : Set E} (hs : s ∈ 𝓝 x) {u v : E → ℝ} (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (hh : 0 ≤ u x) (he : ∀ t : Set E, IsCompact t → t ⊆ s →
      (∫⁻ y in t, ENNReal.ofReal (u y)) = ∫⁻ y in t, ENNReal.ofReal (v y)) : v x ≤ u x := by
  by_contra! hi
  obtain ⟨a,ha,hb⟩ := exists_between hi
  obtain ⟨b,hw,hm⟩ := exists_between hb
  have h0 : ∀ᶠ y in 𝓝 x, y∈s ∧ u y<a ∧ b<v y := (show ∀ᶠ y in 𝓝 x, y∈s from hs).and
    ((hu.eventually (gt_mem_nhds ha)).and (hv.eventually (lt_mem_nhds hm)))
  obtain ⟨r,hr,hy⟩ := nhds_basis_closedBall.mem_iff.mp h0
  let t := closedBall x r
  have ht := isCompact_closedBall x r
  have hl : t ⊆ s := fun _ hx => (hy hx).1
  have hp : 0 < volume t := lt_of_lt_of_le (isOpen_ball.measure_pos volume ⟨x,mem_ball_self hr⟩) (measure_mono ball_subset_closedBall)
  apply (he t ht hl).not_lt
  calc
    _ ≤ ∫⁻ _ : E in t, ENNReal.ofReal a := setLIntegral_mono' ht.measurableSet (fun _ hx => ENNReal.ofReal_le_ofReal (hy hx).2.1.le)
    _ < ∫⁻ _ : E in t, ENNReal.ofReal b := by
      simp only [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_mul_left hp.ne' ht.measure_lt_top.ne ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hh.trans ha.le)).mpr hw)
    _ ≤ _ := setLIntegral_mono' ht.measurableSet (fun _ hx => ENNReal.ofReal_le_ofReal (hy hx).2.2.le)

lemma ratio_even {Z : ChartRatio G} (h : LocalRatio Z) {x : G.Color} (hx : x∈ball 0 Z.radius) :
    Z.J x = Z.J (-x) := by
  let u := fun y : G.Color => Z.scale*Z.J y
  have he {x : G.Color} (hx : x∈ball 0 Z.radius) : Z.J (-x) ≤ Z.J x := by
    apply le_of_mul_le_mul_left _ h.scale
    apply price_le_of_caps (s:=ball 0 Z.radius) (isOpen_ball.mem_nhds hx) (u:=u) (v:=fun y => u (-y))
      (continuousAt_const.mul (h.germ x hx).continuousAt) ?_ (mul_pos h.scale (h.pos _ hx)).le (opposite_cap h)
    have hh : ContinuousAt u (-x) := continuousAt_const.mul (h.germ _ (by simpa using hx)).continuousAt
    exact hh.comp continuous_neg.continuousAt
  exact le_antisymm (by simpa using he (x:=-x) (by simpa using hx)) (he hx)

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma still_even {u : E → ℝ} (h : DifferentiableAt ℝ u 0)
    (he : ∀ᶠ x in 𝓝 (0:E), u (-x)=u x) (y : E) : HasDerivAt (fun v : ℝ => u (v • y)) 0 0 := by
  have ht := YM.Push.side u h y
  have hp : HasDerivAt (fun v : ℝ => u ((-v) • y)) (-(fderiv ℝ u 0 y)) 0 := by
    have hx : HasDerivAt (fun v : ℝ => u (v • y)) (fderiv ℝ u 0 y) (-0) := by rw [neg_zero]; exact ht
    simpa only [Function.comp_def,neg_mul,mul_neg,mul_one, smul_eq_mul] using hx.comp (0:ℝ) (hasDerivAt_neg' (0:ℝ))
  have hv : (fun v : ℝ => u (v • y)) =ᶠ[𝓝 (0:ℝ)] (fun v => u ((-v) • y)) := by
    have hw : Tendsto (fun v : ℝ => v • y) (𝓝 0) (𝓝 0) := by
      simpa using! (show Continuous fun v : ℝ => v • y from by fun_prop).tendsto 0
    filter_upwards [hw.eventually he] with v hb
    simp only [neg_smul, hb]
  have hi := ht.unique (hp.congr_of_eventuallyEq hv)
  have hz : fderiv ℝ u 0 y=0 := by linarith
  rw [hz] at ht; exact ht

lemma price_even_germ {u : E → ℝ} (h : AnalyticAt ℝ u 0)
    (he : ∀ᶠ x in 𝓝 (0:E), u (-x)=u x) :
    ∃ D r : ℝ, 0 < D ∧ 0 < r ∧ ∀ x : E, ‖x‖ ≤ r → |u x - u 0| ≤ D*‖x‖^2 := by
  obtain ⟨D,r,hD,hr,hC⟩ := Fluctuations.chart_quadratic_cost u (fun _ => 0) h (still_even (h.differentiableAt) he)
  exact ⟨D,r,hD,hr,fun x hx => by simpa [Real.norm_eq_abs] using (hC x).2 hx⟩
end

/-- Actual quadratic prices (∃ pre-L uniform C and chart radius).
No factors depending on how many lattice links in the patch. -/
theorem ratio_price {Z : ChartRatio G} (h : LocalRatio Z) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < Z.radius ∧
    ∀ x : G.Color, ‖x‖ ≤ r → 0 < Z.J x ∧ |Z.J x-1| ≤ C*‖x‖^2 ∧ |Real.log (Z.J x)| ≤ C*‖x‖^2 := by
  have hb : ∀ᶠ x in 𝓝 (0:G.Color), x ∈ ball 0 Z.radius := ball_mem_nhds (0:G.Color) h.patch
  have he : ∀ᶠ x in 𝓝 (0:G.Color), Z.J (-x)=Z.J x := hb.mono fun i hi => (ratio_even h hi).symm
  have hf : ContDiffAt ℝ ω Z.J 0 := h.germ _ (mem_ball_self h.patch)
  obtain ⟨D,r,hD,hr,hF⟩ := price_even_germ hf.analyticAt he
  have hi : ContDiffAt ℝ ω (fun x : G.Color => Real.log (Z.J x)) 0 := hf.log (by rw [h.anchored]; norm_num)
  obtain ⟨N,n,hN,hn,hC⟩ := price_even_germ hi.analyticAt (he.mono (fun i hh => congr_arg _ hh))
  let t := min (Z.radius / 2) (min r n)
  have ht : t < Z.radius := (min_le_left _ _).trans_lt (half_lt_self h.patch)
  refine ⟨max D N,t, hD.trans_le (le_max_left ..), lt_min (half_pos h.patch) (lt_min hr hn),ht,?_⟩
  intro x hx
  have hk := (hx.trans (min_le_right _ _))
  refine ⟨h.pos x (by simpa using hx.trans_lt ht),?_,?_⟩
  · rw [← h.anchored]
    exact (hF x (hk.trans (min_le_left _ _))).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (sq_nonneg _))
  change ∀ a, _ at hC
  simp only [h.anchored, Real.log_one, sub_zero] at hC
  exact (hC x (hk.trans (min_le_right _ _))).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg _))



end YM.Next.SectorChange
