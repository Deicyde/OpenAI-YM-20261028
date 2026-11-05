import YM.Extra.WEAK_SCALING_ACTLAW.Comparisons

/-!
# Fixed-cap common comparison requests; free inclusion & derivative matrix limits

Use finite detectors with support in the coordinate-generic part of Conf.
Such smears detect already in the free quotient, including the real-life
possibility of spectator weights above the input cap. No change of b/maps/
physical scheme between the input and output cap tests. Read r*deriv by
actual IBP in rescaled positions; infer convergence of the fitted matrices
without assuming an inverse bound in the physical coordinate norm. This is
not yet exact alignment of inclusions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Set Function Filter MeasureTheory Extraction Climb Ward Table Spec
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {L : Register G} {S : Table L} {n d e : ℕ}

lemma Follows.smear (t : Test n) {O : Set (Points n)} (he : tsupport t ⊆ O) {F : ℕ → Points n → ℂ}
    (hc : ∀ k, ContinuousOn (F k) (conf n)) {g : Points n → ℂ} (hg : ContinuousOn g (conf n)) (h : Follows O F g) :
    Tendsto (fun k => t.applyTo (F k)) atTop (𝓝 (t.applyTo g)) := by
  have ht := t.hasCompactSupport
  have hgc := hg.mono t.tsupport_subset
  obtain ⟨B,hB⟩ := ht.exists_bound_of_continuousOn hgc
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖t x‖*(B+1))
    (Eventually.of_forall (fun k => (t.smearing (hc k)).aestronglyMeasurable))
  · filter_upwards [h.onCompact ht he hgc one_pos] with i hi
    filter_upwards with x
    rw [norm_mul]
    by_cases hx : x ∈ tsupport t
    · gcongr
      linarith [hi x hx,hB x hx,norm_sub_norm_le (F i x) (g x)]
    rw [image_eq_zero_of_notMem_tsupport hx,norm_zero,zero_mul,zero_mul]
  · exact (t.continuous.integrable_of_hasCompactSupport ht).norm.mul_const _
  filter_upwards with x
  by_cases hx : x ∈ tsupport t
  · exact tendsto_const_nhds.mul (h id tendsto_id x (he hx) (fun _ => x) tendsto_const_nhds)
  simp [image_eq_zero_of_notMem_tsupport hx]

lemma null_on_generic {K : Points n → ℂ} (h : ContinuousOn K (conf n))
    (he : ∀ t : Test n, tsupport t ⊆ generic n → t.applyTo K = 0) : EqOn K 0 (conf n) := by
  have ho := genericOpen n
  have hc := h.mono (generic_conf n)
  have ht := ho.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ:=volume) (hc.locallyIntegrableOn ho.measurableSet)
  apply Order.equal h continuousOn_const
  apply Measure.eqOn_open_of_ae_eq (μ:=volume) _ ho hc continuousOn_const
  refine (ae_restrict_iff' ho.measurableSet).mpr (ht ?_)
  intro f hf hf' H
  let g := Complex.ofRealCLM ∘ f
  have hu : tsupport g ⊆ tsupport f := tsupport_comp_subset (map_zero Complex.ofRealCLM) f
  have hg := hu.trans H
  let t : Test n := ⟨g, Complex.ofRealCLM.contDiff.comp hf, hf'.comp_left (map_zero Complex.ofRealCLM),
    hg.trans (generic_conf n)⟩
  rw [← he t hg]; exact integral_congr_ae (Eventually.of_forall fun x => Complex.real_smul)

/-- Evaluate smears in separated *rescaled* positions. No contact terms. -/
def rescale (r : ℝ) (w : Fin n → S.Tag) (B : S.Field d) (x : Points (n+1)) :=
    disc (Fin.cons ⟨d,B⟩ w) (r • x)

lemma rescale_smooth (H : S.Hierarchy) {r : ℝ} (hr : 0 < r) (w : Fin n → S.Tag) (B : S.Field d) :
    ContDiffOn ℝ ∞ (rescale r w B) (conf (n+1)) := fun x hx =>
  ((cont_disc H _ (Work.A04.scale_conf r hr hx)).comp x
    (show ContDiffAt ℝ ∞ (fun x : Points (n+1) => r • x) x by fun_prop)).contDiffWithinAt

def heard (H : S.Hierarchy) {r : ℝ} (hr : 0 < r) (w : Fin n → S.Tag) (t : Test (n+1)) (d : ℕ) : S.Field d →ₗ[ℂ] ℂ := by
  have hF (B : S.Field d) : Integrable (fun x => t x * (Work.A15.front (r • x) w d) B) := by
    simp_rw [Work.A15.front_apply]; exact t.smearing (rescale_smooth H hr w B).continuousOn
  refine { toFun := fun B => ∫ x, t x * (Work.A15.front (r • x) w d) B
           map_add' := fun u v => ?_
           map_smul' := fun c u => ?_ }
  · simp_rw [map_add,mul_add]; exact integral_add (hF _) (hF _)
  change _ = c * (∫ x, _)
  simp_rw [map_smul,smul_eq_mul,mul_left_comm (t _) c]; exact integral_const_mul ..

lemma heard_apply (H : S.Hierarchy) {r : ℝ} (hr : 0 < r) (w : Fin n → S.Tag) (t : Test (n+1)) (B : S.Field d) :
    heard H hr w t d B = t.applyTo (rescale r w B) := by
  dsimp only [heard,LinearMap.coe_mk,AddHom.coe_mk,Test.applyTo,rescale,disc]
  simp_rw [Work.A15.front_apply]

lemma heard_one (H : S.Hierarchy) (w : Fin n → S.Tag) (t : Test (n+1)) (B : S.Field d) :
    heard H one_pos w t d B = t.applyTo (disc (Fin.cons ⟨d,B⟩ w)) := by
  rw [heard_apply]; exact congrArg t.applyTo (by funext x; simp [rescale])

lemma read_inclusion (H : S.Hierarchy) {V : DiffPlan S} (h : V.Inclusions S) {r : ℝ} (hr : 0 < r)
    (w : Fin n → S.Tag) (t : Test (n+1)) (u : d ≤ e) (B : S.Field d) :
    heard H hr w t e (V.rise u B) = heard H hr w t d B := by
  rw [heard_apply,heard_apply]; exact t.apply_eq fun _ hx => h.kernels u B (Work.A04.scale_conf r hr hx) w

lemma read_derivative (H : S.Hierarchy) {V : DiffPlan S} (h : V.Derivatives S) {r : ℝ} (hr : 0 < r)
    (w : Fin n → S.Tag) (t : Test (n+1)) (B : S.Field d) (a : Axis) :
    heard H hr w t (d+1) (r • V.deriv d a B) = -heard H hr w (Dash.down t 0 a) d B := by
  rw [heard_apply,heard_apply, ← Dash.compactTest (rescale_smooth H hr w B)]
  apply t.apply_eq
  intro x hx
  have hw := Work.A04.scale_conf r hr hx
  change _ = Points.gradient 0 a (fun y => disc _ (r • y)) x
  rw [Work.A04.gradient_scaled r _ x ((cont_disc H _ hw).differentiableAt (by simp))]
  unfold rescale disc
  rw [← Work.A15.front_apply, ← h.kernels _ a B hw]
  exact ((Work.A15.front _ w (d+1)).restrictScalars ℝ).map_smul r _ |>.trans
    (congrArg (fun z => r • z) (Work.A15.front_apply ..))

section free
variable {S : Table C.book}

structure Probe (C : Family G) where
  n : ℕ
  w : Fin n → (Free C).Tag
  t : Test (n+1)
  clear : tsupport t ⊆ generic (n+1)

variable (H : (Free C).Hierarchy)

def rows (E : Probe C) (d : ℕ) : (Free C).Field d →ₗ[ℂ] ℂ := heard H one_pos E.w E.t d
lemma detected (d : ℕ) : Injective (LinearMap.pi (fun e => rows H e d)) := by
  apply LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)
  intro v hv
  apply (Free C).field_ext H.laws.toSymmetric
  intro n q x hx; rw [← Work.A15.front_apply (B:=0),map_zero]
  apply null_on_generic ((Free C).class_smooth (Free C) H.smooth (Fin.cons ⟨d,v⟩ q)).continuousOn ?_ hx
  intro t ht; change t.applyTo (disc _) = 0; rw [← heard_one H]
  exact congrFun hv (⟨n,q,t,ht⟩ : Probe C)

/-- Need room for reading at each receiving cap separately, not claiming
spectator weights ≤ that same cap. -/
def Equipped (e M D : ℕ) (Q : ℝ) : Prop := ∃ s : Finset (Probe C),
    Injective (LinearMap.pi fun i : s => rows H i.val e) ∧ ∀ i ∈ s,
      i.n+1 ≤ M ∧ capped D i.w ∧ tsupport i.t ⊆ clearance Q (i.n+1)

lemma equipment (E m : ℕ) (R : ℝ) : ∃ (M D : ℕ) (Q : ℝ), m ≤ M ∧ E ≤ D ∧ R < Q ∧ 0 < Q ∧
    ∀ d ≤ E, Equipped H d M D Q := by
  choose s hs using fun d => Work.A04.finite_faithful _ (detected H d)
  have hm (d) := (eventually_all_finset (s d)).mpr (fun i _ => eventually_ge_atTop (i.n+1))
  have hd d := (eventually_all_finset (s d)).mpr (fun i _ => eventually_all.mpr (fun j => eventually_ge_atTop (i.w j).1))
  have hQ d := (eventually_all_finset (s d)).mpr (fun i _ => eventually_clear i.t.hasCompactSupport i.clear)
  obtain ⟨M,hM,hM'⟩ := ((eventually_ge_atTop m).and ((eventually_all_finset (Finset.Iic E)).mpr fun d _ => hm d)).exists
  obtain ⟨D,hD,hD'⟩ := ((eventually_ge_atTop E).and ((eventually_all_finset (Finset.Iic E)).mpr fun d _ => hd d)).exists
  obtain ⟨Q,⟨hq,hq'⟩,hQ'⟩ := (((eventually_gt_atTop R).and (eventually_gt_atTop 0)).and
    ((eventually_all_finset (Finset.Iic E)).mpr fun d _ => hQ d)).exists
  exact ⟨M,D,Q,hM,hD,hq,hq',fun d hd => ⟨s d,hs d,fun i hi =>
    ⟨hM' d (by simpa) i hi,hD' d (by simpa) i hi,hQ' d (by simpa) i hi⟩⟩⟩

/-- Only an arity/weight/window-specific weak coordinate survey. -/
structure Survey (S : Table C.book) (hs : S.RealSpin) (h : (Free C).RealSpin) (M D : ℕ) (Q : ℝ) where
  r : ℕ → ℝ
  pos k : 0 < r k
  shrinks : Tendsto r atTop (𝓝 0)
  delta : ℕ → ℝ
  positive k : 0 < delta k
  fine : Tendsto delta atTop (𝓝 0)
  U : Maps S
  mirror k d : d ≤ D → ∀ g v, U k d ((Free C).mirror h d g v) = S.mirror hs d g (U k d v)
  conj k d : d ≤ D → ∀ v, U k d ((Free C).conj h d v) = S.conj hs d (U k d v)
  unit k d : d ≤ D → U k d ((Free C).unit d) = S.unit d
  sampled n : n ≤ M → ∀ v : Fin n → (Free C).Tag, capped D v → Sampled (apart Q n) delta (readMap U r v) (disc v)
  growth n : n ≤ M → ∀ v : Fin n → (Free C).Tag, capped D v → Follows (apart Q n) (fun k x => delta k • readMap U r v k x) 0
  observes n : n ≤ M → ∀ v : Fin n → (Free C).Tag, capped D v → Follows (clearance Q n) (readMap U r v) (disc v)

variable {f : Order} {hs : S.Hierarchy} {M D : ℕ} {Q : ℝ} {H}

def Retained.survey {b : Stations C} (Z : Retained b f) (s : Seed C f S) {h} (hq : 0 < Q) (hC : FiniteCosts b f h M D Q) :
    Survey S s.kernel.spin h M D Q :=
  ⟨b.r, b.positive,b.shrinks,b.delta,fun _ => div_pos (C.S.a_pos _) (b.positive _),b.fine,Z.maps S,
    fun k d hd => (Z.marks hC s.kernel.spin k d hd).1,
    fun k d hd => (Z.marks hC s.kernel.spin k d hd).2.1,
    fun k d hd => (Z.marks hC s.kernel.spin k d hd).2.2,
    fun _ hn _ hv => Z.on_grid s hC.aligned hq hn hv, fun _ hn _ hv => Z.growth s hC.center hq hn hv,
    fun _ hn _ hv => Z.on_clearance s hC.center hC.aligned hq hn hv⟩

lemma dimension_le (h : Seed C f S) (d : ℕ) : Module.finrank ℂ (S.Field d) ≤ Module.finrank ℂ ((Free C).Field d) := by
  classical
  obtain ⟨X,Z,hZ⟩ := h.corrected d
  obtain ⟨k,hk⟩ := hZ.span.exists
  let x := S.project d ∘ Z.later k
  change Submodule.span ℂ (range x) = ⊤ at hk
  rw [← finrank_top,← hk,Module.finrank_eq_card_basis X.basis]
  exact (finrank_span_le_card (R:=ℂ) (range x)).trans (by rw [toFinset_range]; exact Finset.card_image_le.trans_eq (Finset.card_univ))

namespace Survey
variable (hs : S.Hierarchy) {hS : S.RealSpin} {h : (Free C).RealSpin} (b : Survey S hS h M D Q)

def watchers (E : Probe C) (t : Test (E.n+1)) (d k : ℕ) : (Free C).Field d →ₗ[ℂ] ℂ :=
  (heard hs (b.pos k) (routed b.U k ∘ E.w) t d).comp (b.U k d)

lemma watched (H : (Free C).Hierarchy) (E : Probe C) (t : Test (E.n+1)) (d : ℕ) (hd : d≤D) (hn : E.n+1 ≤ M) (hw : capped D E.w)
    (hc : tsupport t ⊆ clearance Q (E.n+1)) (x : (Free C).Field d) :
    Tendsto (fun k => b.watchers hs E t d k x) atTop (𝓝 (heard H one_pos E.w t d x)) := by
  let v : Fin (E.n+1) → (Free C).Tag := Fin.cons (⟨d,x⟩ : (Free C).Tag) E.w
  have he (k : ℕ) : b.watchers hs E t d k x = t.applyTo (readMap b.U b.r v k) := by
    rw [watchers, LinearMap.comp_apply, heard_apply]; congr 1; funext y
    rw [rescale, readMap]; simp only [v, Fin.comp_cons]; rfl
  simp_rw [he,heard_one]
  exact (b.observes _ hn v (Fin.cases hd hw)).smear _ hc
    (fun k y hy => (readMap_smooth hs (b.pos k) hy).continuousAt.continuousWithinAt)
    ((Free C).class_smooth (Free C) H.smooth v).continuousOn

lemma eventually_bijective (s : Seed C f S) (hd : d ≤ D) (h : Equipped H d M D Q) :
    ∀ᶠ k : ℕ in atTop, Bijective (b.U k d) := by
  classical
  obtain ⟨T,hT,hw⟩ := h
  let F (k : ℕ) := LinearMap.pi fun i : T => b.watchers s.kernel i.val i.val.t d k
  have hf x : Tendsto (fun k => F k x) atTop (𝓝 ((LinearMap.pi (fun i : T => rows H i.val d)) x)) := tendsto_pi_nhds.mpr (fun i : T => b.watched s.kernel H i.val i.val.t d hd (hw _ i.property).1
    (hw _ i.property).2.1 (hw _ i.property).2.2 x)
  have he := Dash.fit_plane F (LinearMap.pi fun i : T => rows H i.val d) hf
  filter_upwards [he.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds (show _ from hT))] with k hk
  have hu : Injective (b.U k d) := fun i j hij => hk (funext fun t => congrArg (heard s.kernel (b.pos k) _ _ _) hij)
  exact ⟨hu,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm
    (LinearMap.finrank_le_finrank_of_injective hu) (dimension_le s d))).1 hu⟩

open scoped Classical in
def charts (hF : ∀ d, Nonempty (YM.Spin.change S d)) (k d : ℕ) : YM.Spin.change S d :=
    if h : Bijective (b.U k d) then LinearEquiv.ofBijective _ h else Classical.choice (hF d)
lemma equals {k d : ℕ} (hF : ∀ d, Nonempty (YM.Spin.change S d)) (h : Bijective (b.U k d)) (v) :
    b.charts hF k d v = b.U k d v := by rw [charts,dif_pos h]; rfl

variable (s : Seed C f S) (hF : ∀ d, Nonempty (YM.Spin.change S d))
include s

lemma inc_limit (V : DiffPlan S) (W : DiffPlan (Free C)) (hV : V.Inclusions S) (hW : W.Inclusions (Free C))
    (e : d ≤ d+1) (hd : d+1 ≤ D) (h : Equipped H (d+1) M D Q) (h' : Equipped H d M D Q) (v : (Free C).Field d) :
    Tendsto (fun k => (b.charts hF k (d+1)).symm (V.rise e (b.charts hF k d v))) atTop (𝓝 (W.rise e v)) := by
  classical
  obtain ⟨T,hT,hw⟩ := h
  apply Work.A04.tendsto_of_fitted (fun k => LinearMap.pi fun i : T => b.watchers s.kernel i.val i.val.t (d+1) k) _ hT
    (fun x => tendsto_pi_nhds.mpr fun i : T => b.watched s.kernel H i.val i.val.t (d+1) hd (hw _ i.property).1
      (hw _ i.property).2.1 (hw _ i.property).2.2 x)
  refine tendsto_pi_nhds.mpr fun i => ?_
  obtain ⟨hn,hv,he⟩ := hw _ i.property
  change Tendsto _ _ (𝓝 (heard H one_pos _ _ _ _)); rw [read_inclusion H hW one_pos]
  apply (b.watched s.kernel H i.val i.val.t d (by omega) hn hv he v).congr'
  filter_upwards [b.eventually_bijective s (by omega : d≤D) h',b.eventually_bijective (H:=H) s hd ⟨T,hT,hw⟩] with k h₁ h₂
  change _ = b.watchers s.kernel i.val i.val.t _ _ _
  rw [watchers,LinearMap.comp_apply,watchers,LinearMap.comp_apply,← b.equals hF h₂, LinearEquiv.apply_symm_apply,
    b.equals hF h₁,read_inclusion s.kernel hV]

lemma deriv_limit (V : DiffPlan S) (W : DiffPlan (Free C)) (hV : V.Derivatives S) (hW : W.Derivatives (Free C))
    (hd : d+1 ≤ D) (h : Equipped H (d+1) M D Q) (h' : Equipped H d M D Q) (v : (Free C).Field d) (a : Axis) :
    Tendsto (fun k => (b.charts hF k (d+1)).symm (b.r k • V.deriv d a (b.charts hF k d v))) atTop (𝓝 (W.deriv d a v)) := by
  classical
  obtain ⟨T,hT,hw⟩ := h
  apply Work.A04.tendsto_of_fitted (fun k => LinearMap.pi fun i : T => b.watchers s.kernel i.val i.val.t (d+1) k) _ hT
    (fun x => tendsto_pi_nhds.mpr fun i : T => b.watched s.kernel H i.val i.val.t (d+1) hd (hw _ i.property).1
      (hw _ i.property).2.1 (hw _ i.property).2.2 x)
  refine tendsto_pi_nhds.mpr fun i => ?_
  obtain ⟨hn,hv,he⟩ := hw _ i.property
  have hd' := read_derivative H hW one_pos i.val.w i.val.t v a
  rw [one_smul] at hd'
  change Tendsto _ _ (𝓝 (heard H one_pos _ _ _ _)); rw [hd']
  apply ((b.watched s.kernel H i.val (Dash.down i.val.t 0 a) d (by omega) hn hv ((tsupport_fderiv_apply_subset ℝ _).trans he) v).neg).congr'
  filter_upwards [b.eventually_bijective s (by omega : d≤D) h',b.eventually_bijective (H:=H) s hd ⟨T,hT,hw⟩] with k h₁ h₂
  change _ = b.watchers s.kernel i.val i.val.t _ _ _
  rw [watchers,LinearMap.comp_apply,watchers,LinearMap.comp_apply,← b.equals hF h₂,LinearEquiv.apply_symm_apply,
    b.equals hF h₁,read_derivative s.kernel hV]
end Survey
end free
end YM.Extra.WeakScaling
