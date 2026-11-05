import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Rate

/-!
# Windows buying uniformity of the actual likelihood off holes

Canonical gauges, preserve real held Haar input. Pay in chord units
with thresholds of the same `Branches`. No copying Q over overlaps.
Our discrete tagged factors are relative to a priori uniform probabilities
on their physical alphabets; not absent when off the original sector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Rates
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma frame_use (D : Patch) (K : KernelChoices) (h : D.Branches K G) : D.usesMin K (1:CoverConfig G) ∧ D.selected (1:CoverConfig G)=1 := by
  let S : StepData D.L (D.L*D.L) := ⟨D,K,rfl⟩
  have hp := Push.picks S 0 (G:=G); rw [Push.product_zero] at hp
  refine ⟨hp,?_⟩
  let U := Push.product S 0 (0:Push.In G (D.L*D.L))
  funext i; let t : S.SitesChoice := Classical.ofNonempty
  have hm : D.frame K U (t 0) i=1 := G.mat_injective (Push.hats_zero S (h:=h) 0 t i)
  rwa [show U=(1:CoverConfig G) from Push.product_zero .., Patch.frame, if_pos (show D.usesMin K _ from hp)] at hm

lemma best_use (D : Patch) (K : KernelChoices) (h : D.Branches K G) : D.usesBest K (1:D.Connector G) ∧ D.best (1:D.Connector G)=1 := by
  let Y : D.Connector G := 1
  have he : D.bondCost Y 1=0 := by simp [Y,bondCost]
  have hp : D.usesBest K Y := lt_of_le_of_lt ((D.bond_min Y).choose_spec 1) (he.symm ▸ K.predictor_cut_pos)
  refine ⟨hp,(h.predictor_unique _ hp).unique (D.bond_min _).choose_spec fun v => ?_⟩
  rw [he]; exact Finset.sum_nonneg fun i _ => mul_nonneg (D.weight_nonneg _) (G.price_range _).1

private def bridgeOf (D : Patch) (l : Axis) (U : CoverConfig G) (f h : D.Frame G) : D.Connector G :=
    fun x => f x * travel U x.val (List.replicate D.L.val (posDir l)) * (h x)⁻¹

private theorem frame_opens (D : Patch) (K : KernelChoices) (h : D.Branches K G) (δ : ℝ) (he : 0 < δ) (j : Axis) :
    ∀ᶠ x : CoverConfig G × CoverConfig G in 𝓝 (1,1), D.usesMin K x.1 ∧ D.usesMin K x.2 ∧
      ∀ l r : D.FrameTag, let U := bridgeOf D j x.1 (D.frame K x.1 l) (D.frame K x.2 r)
        D.usesBest K U ∧ ∀ t : D.Points, G.chord (D.predict K U t) < δ := by
  let o : CoverConfig G := 1
  let F := fun x : CoverConfig G × CoverConfig G => bridgeOf D j x.1 (D.selected x.1) (D.selected x.2)
  obtain ⟨hA,hY⟩ := frame_use D K h
  obtain ⟨hB,hZ⟩ := best_use D K h
  have hu : {u : CoverConfig G|D.usesMin K u}∈ nhds o := D.min_open.mem_nhds hA
  have hx := (D.selected_cont h).continuousAt hu
  have hf : ContinuousAt F (o,o) := by
    apply continuousAt_pi.mpr; intro i
    refine (((continuous_apply i).continuousAt.comp (hx.comp (continuousAt_fst (p:=(o,o))))).mul ?_).mul
      (((continuous_apply i).continuousAt.comp (hx.comp (continuousAt_snd (p:=(o,o))))).inv)
    exact (continuous_travel _ _).continuousAt.comp continuousAt_fst
  have hc : F (o,o)=1 := by
    funext x; simp only [F,bridgeOf, o,hY,Pi.one_apply,Pressure.one,mul_one,inv_one]
  have hv : {y : D.Connector G | D.usesBest K y} ∈ nhds (F (o,o)) := by rw [hc]; exact D.best_open.mem_nhds hB
  have hj : ContinuousAt (fun x => G.chord (D.best (F x))) (o,o) :=
    (show Continuous G.chord by fun_prop).continuousAt.comp (((D.best_cont h).continuousAt hv).comp hf)
  filter_upwards [continuousAt_fst.tendsto (x:=(o,o)) hu,continuousAt_snd.tendsto (x:=(o,o)) hu,hf.tendsto hv,
    hj.tendsto.eventually (eventually_lt_nhds (show G.chord (D.best (F (o,o))) < δ by rw [hc,hZ,G.chord_one]; exact he))]
    with x h1 h2 h3 h4
  refine ⟨h1,h2,fun l r => ?_⟩
  dsimp only [Patch.frame]; rw [if_pos (show D.usesMin K x.1 from h1), if_pos (show D.usesMin K x.2 from h2)]
  exact ⟨h3,fun p => by change G.chord (D.predict K (F x) p) < δ; rw [predict, if_pos (show D.usesBest K (F x) from h3)]; exact h4⟩

lemma patch_scope {W : Set (CoverConfig G)} (h : W ∈ nhds (1:CoverConfig G)) (D : Patch) (p : ℕ) : ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (U : Config G f) (y : Site c), (∀ i : Bond f, separation y (home S i) ≤ radiusB x/4 →
      G.chord (U i) ≤ allowance G D x 1 p) → expandAt (S.ratio.embed y) U ∈ W := by
  simp only [nhds_pi, Filter.mem_pi'] at h
  obtain ⟨I,v,hv,ht⟩ := h
  have he i : ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f) (U : Config G f) (y : Site c), (∀ i : Bond f,
        separation y (home S i) ≤ radiusB x/4 → G.chord (U i) ≤ allowance G D x 1 p) → expandAt (S.ratio.embed y) U i∈ v i := by
    obtain ⟨s,hs,hS⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 (hv i)
    let w := route 0 i.1 1
    have hy : Tendsto (fun x => G.colorScale * allowance G D x 1 p) atTop (nhds 0) := by
      simpa only [mul_zero] using! (vanishes G D p).const_mul G.colorScale
    filter_upwards [hy.eventually (ge_mem_nhds hs), Work.E01.radiusB_tendsto.eventually_ge_atTop (4*w.length)] with x hx hp c f S U y he
    apply hS
    let u := expandAt (S.ratio.embed y) U i
    have hh := Work.E03.sep_walk S.ratio.parent (Work.E03.parent_step S) (S.ratio.embed y) w
    have h := Work.E03.stop_route (S.ratio.embed y) 0 i.1
    rw [map_zero,add_zero,add_comm] at h
    rw [show stop _ w = _ from h, S.ratio.embed_parent] at hh
    have ht : G.chord u ≤ allowance G D x 1 p := he (wrap f i.1+S.ratio.embed y, i.2) (hh.trans (by omega))
    rw [Metric.mem_closedBall]; change dist (G.mat u) (G.mat 1) ≤ s
    rw [dist_eq_norm,G.mat_one, ← chord_dist]; exact (mul_le_mul_of_nonneg_left ht G.colorScale_pos.le).trans hx
  filter_upwards [(Filter.eventually_all_finset _).mpr (fun i (_:i∈I) => he i)] with x hx c f S U y hh
  exact ht (fun i hi => hx i hi S U y hh)

/-- Buy the minimizing use on this patch, uniform. Even when other fine
costs lack masks. -/
theorem tap_open (D : Patch) (K : KernelChoices) (h : D.Branches K G) (p : ℕ) (δ : ℝ) (he : 0<δ) :
    ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=D → S.kernel=K →
      ∀ (U : Config G f) (k : S.Choices) (i : Bond c), let B := radiusB x
      (∀ j : Bond f, separation i.1 (home S j) ≤ B/2 → G.chord (U j) ≤ allowance G D x 1 p) →
      S.patch.usesMin K (expandAt (S.ratio.embed i.1) U) ∧ S.patch.usesBest K (S.connector U k.1 i) ∧
        G.chord (S.prediction U k i)<δ := by
  have hh := eventually_all.mpr (fun j : Axis => frame_opens D K h δ he j)
  obtain ⟨s,hs,t,ht,H⟩ := mem_nhds_prod_iff.mp hh
  filter_upwards [patch_scope hs D p, patch_scope ht D p, Work.E01.radiusB_tendsto.eventually_ge_atTop 4]
    with x hx hv hL c f S hS hP U k i B hw
  have h1 := hx S U i.1 (fun j hj => hw j (by unfold B; omega))
  let y := i.1+step i.2
  have h2 := hv S U y (fun j hj => hw j (le_trans (separation_triangle _ y _) ((Nat.add_le_add (b:=1)
    (Work.E03.sep_step i.1 i.2) hj).trans (by unfold B; omega))))
  let W := expandAt (S.ratio.embed i.1) U; let V := expandAt (S.ratio.embed y) U
  have ht := H (show (W,V)∈Set.prod s t from ⟨h1,h2⟩)
  change ∀ j : Axis, _ at ht
  revert h hP; subst D
  intro hd hP
  subst K
  obtain ⟨hn,hW,hc⟩ := ht i.2
  obtain ⟨hm,hX⟩ := hc (k.1 i.1) (k.1 y)
  exact ⟨hn,hm,hX (k.2 i)⟩
end YM.AnalyticNext.ConnectedActivity.Aff
