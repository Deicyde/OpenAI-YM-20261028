import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shell


/-!
# True predictors in small charts

The frames lemma on a particular finite Step is NOT automatically a
uniform-in-torus branch receipt. Need actual likelihood estimates also
when some defaults have been peeled. Work off the numerical hull in a
local gauge, not using group logarithm inferred from k-values. Need
`δ` as post-L input; can make arbitrarily small then adjust spatial
halo/delay at the same transition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Forward
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations Work.E03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

open Patch

private lemma at_patch (D : Patch) (K : KernelChoices) (h : D.Branches K G) :
    D.usesMin K (1:CoverConfig G) ∧ ∀ j : D.FrameTag, D.frame K (1:CoverConfig G) j=1 := by
  let c : Side := ⟨3,by norm_num⟩
  let S : StepData c (c*D.L) := ⟨D,K,rfl⟩
  have he : Push.product (G:=G) S 0 0=1 := by
    unfold Push.product
    change expandAt _ (represent 0)=(1:CoverConfig G); rw [link_one]; rfl
  constructor
  · rw [← he]; exact Push.picks S _
  intro j
  funext i
  rw [← he];
  let F : S.SitesChoice := fun _ => j
  exact G.mat_injective (Push.hats_zero (G:=G) S 0 F (h:=h) i)

private lemma at_bond (D : Patch) (K : KernelChoices) (h : D.Branches K G) :
    D.usesBest K (1:D.Connector G) ∧ D.best (1:D.Connector G)=1 := by
  let c : Side := ⟨3,by norm_num⟩
  let S : StepData c (c*D.L) := ⟨D,K,rfl⟩
  let t : S.Choices := Classical.arbitrary _
  let i : Bond c := Classical.arbitrary _
  have he : S.connector 1 t.1 i=(1:S.patch.Connector G) := by
    rw [← link_one]
    exact funext fun j => Push.deck_zero S h _ _ j
  have hb : D.usesBest K (1:D.Connector G) := by
    apply lt_of_le_of_lt ((D.bond_min _).choose_spec 1)
    simpa [Patch.bondCost] using K.predictor_cut_pos
  refine ⟨hb,?_⟩
  have hp := Push.settled S h i t
  rw [StepData.prediction,he,Patch.predict,if_pos (show S.patch.usesBest S.kernel (1:S.patch.Connector G) from hb)] at hp
  exact hp

-- Uniform chord-neighborhood over these finite alphabets.
private def testDeck (P : Patch) (K : KernelChoices) (a : Axis) (X : CoverConfig G) (t u : P.FrameTag) : P.Connector G :=
    fun i => P.frame K X t i * travel X i.val (List.replicate P.L.val (posDir a)) *
      (P.frame K (translate (centerRoot P (step a)) X) u i)⁻¹

private lemma deck_eq (U : Config G f) (k : S.Choices) (i : Site c) (a : Axis) :
    S.connector U k.1 (i,a)=testDeck S.patch S.kernel a (expandAt (S.ratio.embed i) U)
      (k.1 i) (k.1 (i+step a)) := by
  have he := Pressure.levels S i U (step a)
  rw [plank,wrap_step,add_comm] at he
  unfold StepData.connector StepData.frames; dsimp only; rw [he]; rfl

private lemma patch_check (P : Patch) (K : KernelChoices) (h : P.Branches K G) {δ : ℝ} (hd : 0<δ) :
    ∀ᶠ X : CoverConfig G in 𝓝 1, P.usesMin K X ∧ ∀ a t u,
      let Y := testDeck P K a X t u
      P.usesBest K Y ∧ ∀ i : P.Points,G.chord (P.predict K Y i)<δ := by
  obtain ⟨he,ht⟩ := at_patch P K h
  obtain ⟨hl,hy⟩ := at_bond P K h
  have hp : ∀ᶠ X : CoverConfig G in 𝓝 1,P.usesMin K X := P.min_open.mem_nhds he
  have hv (i : P.FrameTag) : Tendsto (fun X => P.frame K X i) (𝓝 (1:CoverConfig G)) (𝓝 1) := by
    rw [← ht i]
    have hy' : ContinuousAt P.selected (1:CoverConfig G) := (P.selected_cont h _ he).continuousAt (P.min_open.mem_nhds he)
    have H : (fun X : CoverConfig G => P.frame K X i) =ᶠ[𝓝 1] P.selected := hp.mono fun X hx => if_pos hx
    exact ((hy'.congr H.symm)).tendsto
  refine hp.and (eventually_all.mpr fun a => eventually_all.mpr fun t => eventually_all.mpr fun u => ?_)
  have hX : Tendsto (fun X : CoverConfig G => testDeck P K a X t u) (𝓝 1) (𝓝 1) := by
    let l := List.replicate P.L.val (posDir a)
    let w (X : CoverConfig G) := translate (centerRoot P (step a)) X
    have hz : Tendsto w (𝓝 1) (𝓝 1) := (show Continuous w by unfold w Lattice.translate; fun_prop).tendsto 1
    refine tendsto_pi_nhds.mpr fun i => ?_
    have he' (p : Cover) (l : Walk) : travel (1:CoverConfig G) p l = 1 := by
      induction l generalizing p <;> simp_all [travel, Step.read]
    have hl : Tendsto (fun X : CoverConfig G => travel X i.val l) (𝓝 1) (𝓝 1) := by
      conv_rhs => rw [← he' i.val l]
      exact (continuous_travel l i.val).tendsto (1:CoverConfig G)
    simpa only [Pi.one_apply, inv_one,mul_one,Function.comp_def] using!
      (((tendsto_pi_nhds.mp (hv t) i).mul hl).mul ((tendsto_pi_nhds.mp ((hv u).comp hz) i).inv))
  have hg : G.chord (P.best (1:P.Connector G))<δ := by rw [hy,G.chord_one]; exact hd
  have hc : ContinuousAt P.best (1:P.Connector G) :=
    (P.best_cont h _ hl).continuousAt (P.best_open.mem_nhds hl)
  have hx : ∀ᶠ Y : P.Connector G in 𝓝 1, P.usesBest K Y ∧ G.chord (P.best Y)<δ :=
    (show ∀ᶠ Y : P.Connector G in 𝓝 1,P.usesBest K Y from P.best_open.mem_nhds hl).and
      ((G.continuous_chord.continuousAt.comp hc).eventually (gt_mem_nhds hg))
  filter_upwards [hX.eventually hx] with X hh
  refine ⟨hh.1,fun i => ?_⟩
  rw [Patch.predict,if_pos hh.1]; exact hh.2

/-- Only finitely many links need be clamped to ensure any fixed-L
near-chart use on the cover. Uniform one δ here is relative to
matrix norm. -/
private lemma cover_guard (Y : Set (CoverConfig G)) (h : Y ∈ 𝓝 (1:CoverConfig G)) :
    ∃ r : ℝ, ∃ A : Finset (Edge Cover), 0<r ∧ ∀ U : CoverConfig G,
      (∀ i∈A, G.chord (U i) ≤ r) → U∈Y := by
  rw [nhds_pi, Filter.mem_pi] at h
  obtain ⟨I,hI,t,ht,h⟩ := h
  have he i : t i ∈ 𝓝 (1:G.El) := ht i
  choose b hb hu using fun i => Metric.nhds_basis_closedBall.mem_iff.mp (he i)
  let B := hI.toFinset.image b
  let r := (insert 1 B).min' ⟨_,mem_insert_self ..⟩
  have hv : r∈insert 1 B := min'_mem ..
  have hp : 0 < r := by
    rcases mem_insert.mp hv with hh|hx
    · rw [hh]; norm_num
    obtain ⟨i,-,hi⟩ := mem_image.mp hx; rw [← hi]; exact hb i
  have hg := G.colorScale_pos
  refine ⟨r/G.colorScale,hI.toFinset,div_pos hp hg,fun U hx => h ?_⟩
  intro i hi; apply hu i
  have hf : i∈hI.toFinset := by simpa using hi
  have ht : ‖G.mat (U i)-1‖ ≤ r := by
    rw [← chord_dist,mul_comm]; exact (le_div_iff₀ hg).mp (hx i hf)
  refine Metric.mem_closedBall.mpr ((show dist (U i) (1:G.El) ≤ r from ?_).trans (min'_le _ _ ?_))
  · change dist (G.mat (U i)) (1:G.Mat) ≤ r
    rwa [dist_eq_norm]
  exact mem_insert_of_mem (Finset.mem_image_of_mem _ hf)

/-- Uniform, irrespective of actual old flags and the realization record
away from this stencil. In particular can be applied with tags even
when the U arguments don't realize defaults. -/
theorem approves (P : Patch) (K : KernelChoices) (h : P.Branches K G) {δ : ℝ} (hd : 0<δ) :
    ∃ r : ℝ, ∃ d : ℕ, 0<r ∧ ∀ (c f : Side) (S : StepData c f), S.patch=P → S.kernel=K →
      ∀ U : Config G f, ∀ (k : S.Choices) (y : Site c),
      (∀ i : Bond f, distAt S i y ≤ d → G.chord (U i) ≤ r) → Tags.siteMass U k y=1 ∧
        ∀ a : Axis, G.chord (S.prediction U k (y,a)) ≤ δ ∧ Tags.pinMass U k (y,a)=1 := by
  obtain ⟨r,I,hr,H⟩ := cover_guard _ (patch_check P K h hd)
  let d := I.sup fun i => (route 0 i.1 1).length
  refine ⟨r,d,hr,?_⟩
  rintro c f ⟨P',K',hf⟩ hp hk
  change P'=P at hp; subst P'
  change K'=K at hk; subst K'
  let S : StepData c f := ⟨P,K,hf⟩
  intro U k y hu
  let x := S.ratio.embed y
  let V := expandAt x U
  have ht := H V fun i he => by
    let p := i.1
    let w := route 0 p 1
    have hw : w.length ≤ d := Finset.le_sup (s:=I) (f:=fun i => (route 0 i.1 1).length) he
    apply hu (wrap f p + x,i.2)
    have hp : stop x w=wrap f p+x := by simpa only [map_zero, add_zero, add_comm] using Work.E03.stop_route x 0 p
    have he := Work.E03.sep_walk S.ratio.parent (Work.E03.parent_step S) x w
    rw [hp,S.ratio.embed_parent] at he
    exact he.trans hw
  obtain ⟨hs,hm⟩ : P.usesMin K V ∧ ∀ a t u,
      P.usesBest K (testDeck P K a V t u) ∧
        ∀ i : P.Points, G.chord (P.predict K (testDeck P K a V t u) i)<δ := ht
  constructor
  · change (Fintype.card P.FrameTag:ℝ) * P.frameMass K V _=1
    rw [Patch.frameMass,if_pos hs]; exact mul_inv_cancel₀ (by have := Fintype.card_pos (α:=P.FrameTag); positivity)
  intro a
  have hi := deck_eq (S:=S) U k y a
  change G.chord (S.prediction U k (y,a)) ≤ δ ∧ Tags.pinMass (S:=S) U k (y,a)=1
  rw [Tags.pinMass, StepData.prediction,hi]
  let Z := testDeck S.patch S.kernel a V (k.1 y) (k.1 (y+step a))
  have he : P.usesBest K Z := (hm _ _ _).1
  refine ⟨((hm a _ _).2 _).le,?_⟩
  change (Fintype.card P.Points:ℝ)*P.predictorMass K Z _ = 1
  unfold Patch.predictorMass; rw [if_pos he]
  exact mul_inv_cancel₀ (by have := Fintype.card_pos (α:=P.Points); positivity)
end YM.ConnectedActivityE6.Forward
