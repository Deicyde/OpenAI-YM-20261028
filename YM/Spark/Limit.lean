import YM.Spark.Pile
/-!
# tests varied parameters at edges
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spark
open Set Filter Function MeasureTheory Analysis Boundary
open scoped Topology InnerProductSpace ContDiff BigOperators
variable {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {p : Filter Z} {f : Z → Probe X} {g : Probe X}

-- jointly to zero rather than equicont; arbitrary sets along filters.
lemma packing {Y X : Type*} [TopologicalSpace X] [NormedAddCommGroup Y] (k : Z → X→Y)
    (S : Set X) (H : IsCompact S) (h : ∀ x∈S,Tendsto (Function.uncurry k) (p ×ˢ 𝓝 x) (𝓝 0)) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ z in p,∀ x∈S, ‖k z x‖< ε := by
  classical
  have heq (i : S) : ∃ (U : Set Z) (V : Set X), U ∈ p ∧ IsOpen V ∧ i.val∈ V ∧ ∀ z∈U,∀ x∈V,‖k z x‖<ε := by
    have he' := (h _ i.property).norm.eventually (gt_mem_nhds (by simpa using he : ‖(0:Y)‖<ε))
    obtain ⟨a,ha,b,hb,hx⟩ := mem_prod_iff.mp he'
    obtain ⟨t,ht,hO,Ht⟩ := mem_nhds_iff.mp hb
    exact ⟨a,t,ha,hO,Ht,fun r hr x hy => hx (mk_mem_prod hr (ht hy))⟩
  choose U V hu hV hi Ht using heq
  obtain ⟨s,hp⟩ := H.elim_finite_subcover V hV (fun i h => mem_iUnion.mpr ⟨⟨i,h⟩, hi ⟨i,h⟩⟩)
  filter_upwards [eventually_all_finset s |>.mpr (fun a (_:a∈s) => hu a)] with z hz x hx
  obtain ⟨i,hs,hv⟩ := mem_iUnion₂.mp (hp hx); exact Ht _ z (hz i hs) x hv

lemma ready (h : ∀ n x,Tendsto (fun s : Z × X => jet s.2 n (f s.1)) (p ×ˢ 𝓝 x) (𝓝 (jet x n g)))
    (hp : ∀ i n : ℕ, ∃ C, ∀ᶠ z in p, Probe.size i n (f z) ≤ C) : Tendsto f p (𝓝 g) := by
  refine (Probe.tendN _ _ _).mpr ?_
  intro i j ε he
  obtain ⟨c,hc⟩ := hp (i+1) j
  let b := (ε/2)
  let d := Probe.size (i+1) j g
  obtain ⟨r,hr⟩ := exists_gt (max (0:ℝ) ((c+d)/b))
  have heR : 0<r:= (le_max_left ..).trans_lt hr
  have hR : c+d ≤ b*r := (lt_of_lt_of_eq ((div_lt_iff₀ (show 0<b by dsimp only [b]; positivity)).1 ((le_max_right ..).trans_lt hr)) (mul_comm ..)).le
  let v (z : Z) (x : X) := jet x j (f z-g)
  have hy (x) : Tendsto (Function.uncurry v) (p ×ˢ 𝓝 x) (𝓝 0) := by
    have hx := (g.smooth j).continuous_iteratedFDeriv (m := j) le_rfl
    have hw : Tendsto (fun s : Z × X => jet s.2 j g) (p ×ˢ 𝓝 x) (𝓝 (jet x j g)) := hx.continuousAt.tendsto.comp tendsto_snd
    simpa only [v, Function.uncurry_def,map_sub,sub_self] using! (h j x).sub hw
  filter_upwards [hc, packing v (Metric.closedBall 0 r) (isCompact_closedBall _ _) (fun x _ => hy x) (b/r^i) (by dsimp only [b]; positivity)] with z hz hq
  apply lt_of_le_of_lt (b:=b) _ (half_lt_self he); refine SchwartzMap.seminorm_le_bound ℂ _ _ _ (half_pos he).le (fun x => ?_)
  change ‖x‖^i*‖v z x‖ ≤ _
  by_cases h : ‖x‖≤r
  · have ht := hq x (show x∈Metric.closedBall 0 r by simpa only [Metric.mem_closedBall,dist_zero_right] using h)
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h i) (norm_nonneg _)).trans (mul_comm .. |>.le.trans ((le_div_iff₀ (by positivity)).mp ht.le))
  have ht : r < ‖x‖ := lt_of_not_ge h
  have hL : ‖x‖^(i+1)*‖v z x‖ ≤ b*‖x‖ := (SchwartzMap.le_seminorm ℂ _ _ _ _).trans ((map_sub_le_add (SchwartzMap.seminorm ℂ (i+1) j) (f z) g).trans ((add_le_add_left hz d).trans (hR.trans (mul_le_mul_of_nonneg_left ht.le (half_pos he).le))))
  exact le_of_mul_le_mul_right (a:=‖x‖) (by rwa [mul_right_comm,← pow_succ]) (heR.trans ht)
end YM.Spark
