import YM.EveryPhase.Docks

/-! # The jump is locally constant in the stress time while in range -/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Metric Boundary Next.BOUNDARY Mink Complex Probe
open scoped Topology BigOperators Interval

lemma vertical {A : Type*} [TopologicalSpace A] {f g : A × ℝ → ℂ} {x : A} (M : ℝ)
    (h : ∀ᶠ p in 𝓝 x ×ˢ 𝓝[>] 0, HasDerivAt (fun s => f (p.1,s)) (g p) p.2 ∧ ‖g p‖ ≤ M)
    (hk : ∀ᶠ s : ℝ in 𝓝[>] 0, ContinuousAt (fun t => f (t,s)) x) :
    ∃ y : ℂ, Tendsto f (𝓝 x ×ˢ 𝓝[>] 0) (𝓝 y) := by
  obtain ⟨Z,hZ,W,hW,h⟩ := mem_prod_iff.mp h
  obtain ⟨r,hr,hR⟩ := (nhdsGT_basis_Ioc 0).mem_iff.mp hW
  let N := max 1 M
  have hp : 0<N := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have he (z : A) (hz : z∈Z) (s t) (hs : s∈Ioc 0 r) (ht : t∈Ioc 0 r) :
      dist (f (z,s)) (f (z,t)) ≤ N*|s-t| := by
    have hv (i : ℝ) (hi : i∈Ioc 0 r) := h (show (z,i)∈Z ×ˢ W from ⟨hz,hR hi⟩)
    rw [dist_eq_norm, ← Real.norm_eq_abs]
    exact (convex_Ioc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun s => f (z,s)) (f':=fun j => g (z,j))
      (fun y hy => (hv y hy).1.hasDerivWithinAt) (fun y hy => (hv y hy).2.trans (le_max_right ..)) ht hs
  refine cauchy_map_iff_exists_tendsto.mp (uniformity_basis_dist.cauchy_iff.mpr ⟨inferInstance, ?_⟩)
  intro ε hε
  have hb : ∀ᶠ d in 𝓝[>] (0:ℝ), d≤r := mem_nhdsWithin_of_mem_nhds (ge_mem_nhds hr)
  have hy : ∀ᶠ d in 𝓝[>] (0:ℝ), d<ε/4/N := mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by positivity))
  obtain ⟨d, hd, hw, hb, ht⟩ := (hk.and ((show ∀ᶠ d in 𝓝[>] (0:ℝ), 0<d from self_mem_nhdsWithin).and (hb.and hy))).exists
  refine ⟨ball (f (x,d)) (ε/2),?_,?_⟩
  · refine mem_map.mpr ?_
    filter_upwards [prod_mem_prod hZ ((nhdsGT_basis_Ioc 0).mem_of_mem hw),
      tendsto_fst.eventually (hd (ball_mem_nhds _ (show 0<ε/4 by positivity)))] with p hp₁ hp₂
    change dist (f (p.1,d)) (f (x,d)) < ε/4 at hp₂
    have hz : 0<p.2 ∧ p.2 ≤ d := hp₁.2
    have hy := he _ hp₁.1 p.2 d ⟨hz.1,hz.2.trans hb⟩ ⟨hw,hb⟩
    have hH : dist (f p) (f (p.1,d)) ≤ N*d := hy.trans (mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩) hp.le)
    have hv := (lt_div_iff₀ hp).1 ht
    change dist (f p) (f (x,d)) < ε/2
    linarith [dist_triangle (f p) (f (p.1,d)) (f (x,d))]
  intro a ha b hb
  have hh := dist_triangle_right a b (f (x,d))
  change dist a b < ε
  linarith [mem_ball.mp ha,mem_ball.mp hb]

lemma horizontal {f g : ℝ → ℝ → ℂ} {x y : ℝ} (h : ∀ i∈uIcc x y,
    (∀ᶠ q : ℝ × ℝ in 𝓝[>] 0 ×ˢ 𝓝 i, HasDerivAt (f q.1) (g q.1 q.2) q.2) ∧ Tendsto g.uncurry (𝓝[>] 0 ×ˢ 𝓝 i) (𝓝 0)) :
    Tendsto (fun s => f s y-f s x) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let r := ε/(‖y-x‖+1)
  have hr : 0<r := by unfold r; positivity
  have hC : {p : ℝ × ℝ | HasDerivAt (f p.1) (g p.1 p.2) p.2 ∧ ‖g p.1 p.2‖≤r} ∈ 𝓝[>] 0 ×ˢ 𝓝ˢ (uIcc x y) := by
    refine isCompact_uIcc.mem_prod_nhdsSet_of_forall ?_
    intro p hp
    filter_upwards [(h p hp).1,(h p hp).2.eventually (ball_mem_nhds 0 hr)] with z hz hw
    exact ⟨hz,(lt_of_lt_of_le (by simpa only [Function.uncurry, dist_zero_right] using! mem_ball.mp hw) (le_refl r)).le⟩
  obtain ⟨U,hU,V,hV,h⟩ := mem_prod_iff.mp hC
  filter_upwards [hU] with s hs
  have ht p (hp : p∈uIcc x y) := h (show (s,p)∈U ×ˢ V from ⟨hs,subset_of_mem_nhdsSet hV hp⟩)
  rw [dist_zero_right]
  refine lt_of_le_of_lt ((convex_Icc (min x y) (max x y)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun i hi => (ht i hi).1.hasDerivWithinAt) (fun i hi => (ht i hi).2) left_mem_uIcc right_mem_uIcc) ?_
  calc r * ‖y-x‖ < r*(‖y-x‖+1) := mul_lt_mul_of_pos_left (by linarith) hr
       _ = ε := div_mul_cancel₀ _ (by positivity)

lemma real_path {f : ℂ→ℂ} {u : ℝ→ℂ} {u' f' : ℂ} {p : ℝ}
    (h : HasDerivAt f f' (u p)) (hu : HasDerivAt u u' p) : HasDerivAt (fun s => f (u s)) (u'*f') p :=
    (h.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt p hu

variable {G : Gauge} {L : Register G} {S U : Table L} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D} {P : DiffPlan S} {H : S.RealSpin} {F : Waves S}
  {n : ℕ}

-- Common hypotheses of flux passage. Don't forget Euclidean identities later.
structure Prospect (F : Waves S) (Z : W.Aurora D) (U : Table L) (P : DiffPlan S) (H : S.RealSpin) (T : S.Stress) : Prop where
  hT : Table.Conserved P H T
  hu : U.Hierarchy
  hs : S.Symmetric
  hi : P.Inclusions S
  hd : P.Derivatives U
  hF : F.Region U
  hZ : Z.FullBody F

def crest (Z : W.Aurora D) (K : Killing) (T : S.Stress) (v : Fin n → S.Union) (g : Probe Space3) (k : Fin n)
    (w : Dock n × ℝ) := harbors Z K v T g k.succ w.1.1.1 w.1.1.2 (morn w.1 k w.2)

def trough (Z : W.Aurora D) (K : Killing) (T : S.Stress) (v : Fin n → S.Union) (g : Probe Space3) (k : Fin n)
    (w : Dock n × ℝ) := harbors Z K v T g k.castSucc w.1.1.1 w.1.1.2 (eve w.1 k w.2)

lemma first_ports (K : Killing) (T : S.Stress) (v : Fin n → S.Union) (k : Fin n)
    (p : Dock n) (hp : p.1.2∈strict n) (he : atlases Z (sundial p k) k) (w : Prospect F Z U P H T)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : allows p g k) :
    ∃ a b : ℂ,
      Tendsto (crest Z K T v g k) (𝓝 p ×ˢ 𝓝[>] 0) (𝓝 a) ∧
      Tendsto (trough Z K T v g k) (𝓝 p ×ˢ 𝓝[>] 0) (𝓝 b) := by
  obtain ⟨c,hc,hc'⟩ := tidal_shift K T v k p hp he w.hZ g hg hr
  let A := crest Z K T v g k
  let B := trough Z K T v g k
  have h (j) (z : Dock n → ℂ) (h : Continuous z) (ht : hole j p.1.2 (z p)∈strict (n+1)) :
      ContinuousAt (fun m : Dock n => harbors Z K v T g j m.1.1 m.1.2 (z m)) p := by
    let U := {t : Dock n | hole j t.1.2 (z t)∈strict (n+1)}
    have hX : Continuous (fun t : Dock n => t.1.1) := by fun_prop
    have hu : Continuous (fun t : Dock n => t.1.2) := by fun_prop
    have hU : IsOpen U := (open_strict _).preimage ((hole_hol j).continuous.comp (hu.prodMk h))
    exact (harbors_cont (s:=U) j hX.continuousOn hu.continuousOn h.continuousOn (fun _ h => h) K v T g hg w.hZ).continuousAt (hU.mem_nhds ht)
  have hh j q r z := fun hy => harbors_speed K j v T g hg w.hT w.hu w.hs w.hi w.hd w.hF w.hZ q r z hy
  have ht : Tendsto (fun s : ℝ => (p,s)) (𝓝[>] 0) (𝓝 p ×ˢ 𝓝[>] 0) := tendsto_const_nhds.prodMk tendsto_id
  obtain ⟨a,ha⟩ := vertical (x:=p) (f:=A) (g:=fun x => docks Z K v T g k.succ x.1.1.1 x.1.1.2 (morn x.1 k x.2))
    (‖c‖+1) (by
      filter_upwards [affordable p hp k, hc.norm.eventually (ge_mem_nhds (by simp : ‖c‖<‖c‖+1))] with x hx hq
      refine ⟨?_,hq⟩
      have he : HasDerivAt (morn x.1 k) I x.2 := by
        unfold morn; simpa using ((ofRealCLM.hasDerivAt (x:=x.2)).mul_const I).const_add (town x.1 k)
      have hl := real_path (hh k.succ x.1.1.1 _ _ hx.1) he -- inference ambiguity
      refine hl.congr_deriv ?_; simp [←mul_assoc]) (by
      filter_upwards [ht.eventually (affordable p hp k)] with s hs
      exact h k.succ (fun p => morn p k s) (by unfold morn town; fun_prop) hs.1)
  obtain ⟨b,hb⟩ := vertical (x:=p) (f:=B) (g:=fun x => -docks Z K v T g k.castSucc x.1.1.1 x.1.1.2 (eve x.1 k x.2))
    (‖c‖+1) (by
      filter_upwards [affordable p hp k,hc'.norm.eventually (ge_mem_nhds (by simp : ‖c‖<‖c‖+1))] with x hx hq
      refine ⟨?_,by rw [norm_neg]; exact hq⟩
      have he : HasDerivAt (eve x.1 k) (-I) x.2 := by
        unfold eve; simpa using (hasDerivAt_const x.2 (town x.1 k )).fun_sub ((ofRealCLM.hasDerivAt (x:=x.2)).mul_const I)
      refine (real_path (hh k.castSucc x.1.1.1 _ _ hx.2) he).congr_deriv ?_; simp [←mul_assoc]) (by
      filter_upwards [ht.eventually (affordable p hp k)] with s hs
      exact h k.castSucc (fun p => eve p k s) (by unfold eve town; fun_prop) hs.2)
  exact ⟨a,b,ha,hb⟩

def currentJump (Z : W.Aurora D) (K : Killing) (T : S.Stress) (v : Fin n → S.Union) (g : Probe Space3) (k : Fin n)
    (w : Dock n × ℝ) := crest Z K T v g k w - trough Z K T v g k w

lemma variation (K : Killing) (T : S.Stress) (v : Fin n → S.Union) (k : Fin n)
    (p : Dock n) (hp : p.1.2∈strict n) (he : atlases Z (sundial p k) k) (w : Prospect F Z U P H T)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : allows p g k) :
    Tendsto (fun s => currentJump Z K T v g k (p,s)-currentJump Z K T v g k ((p.1,0),s)) (𝓝[>] 0) (𝓝 0) := by
  let C (t : ℝ) : Dock n := (p.1,t)
  let Y s t := docks Z K v T g k.succ p.1.1 p.1.2 (morn (C t) k s)
  let X s t := docks Z K v T g k.castSucc p.1.1 p.1.2 (eve (C t) k s)
  have hh j q r z := fun hy => harbors_speed K j v T g hg w.hT w.hu w.hs w.hi w.hd w.hF w.hZ q r z hy
  refine horizontal (f:=fun s t => currentJump Z K T v g k (C t,s)) (g:=fun s t => -I*Y s t-(-I*X s t))
    (x:=0) (y:=p.2) ?_
  intro i hi
  have hC : allows (C i) g k := by
    intro j r h
    have hv : |i|≤|p.2| := abs_le.mpr ⟨le_trans (le_min (neg_nonpos.mpr (abs_nonneg _)) (neg_abs_le _)) hi.1,
      le_trans hi.2 (max_le (abs_nonneg _) (le_abs_self _))⟩
    exact hv.trans_lt (hr j r h)
  obtain ⟨c,hc,hb⟩ := tidal_shift K T v k (C i) hp he w.hZ g hg hC
  have hd : Continuous C := continuous_const.prodMk continuous_id
  have hv : Tendsto (fun w : ℝ × ℝ => (C w.2,w.1)) (𝓝[>] 0 ×ˢ 𝓝 i) (𝓝 (C i) ×ˢ 𝓝[>] 0) :=
    ((hd.tendsto i).comp tendsto_snd).prodMk tendsto_fst
  constructor
  · filter_upwards [hv.eventually (affordable (C i) hp k)] with w hw
    have hz : HasDerivAt (fun t => morn (C t) k w.1) 1 w.2 := by
      simpa [morn,town,C] using ((ofRealCLM.hasDerivAt (x:=w.2)).const_add (p.1.2 k)).add_const ((w.1:ℂ)*I)
    have he : HasDerivAt (fun t => eve (C t) k w.1) 1 w.2 := by
      simpa [eve,town,C] using ((ofRealCLM.hasDerivAt (x:=w.2)).const_add (p.1.2 k)).sub_const ((w.1:ℂ)*I)
    have ht := real_path (u:=fun t => morn (C t) k w.1) (hh k.succ p.1.1 p.1.2 _ hw.1) hz
    have hu := real_path (u:=fun t => eve (C t) k w.1) (hh k.castSucc p.1.1 p.1.2 _ hw.2) he
    rw [one_mul] at ht hu
    exact ht.sub hu
  rw [show (0:ℂ)= -I*c - -I*c by ring]
  exact ((hc.comp hv).const_mul (-I)).sub ((hb.comp hv).const_mul (-I))
end YM.EveryPhase.Stress
