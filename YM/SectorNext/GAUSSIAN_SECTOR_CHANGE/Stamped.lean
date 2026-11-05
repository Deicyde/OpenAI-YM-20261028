import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Change
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Intact E late receipts. Before entering scheduling

Stamp for this transformation alone (including legitimacy of reading
some Y links as logs *while on intact prerequisites*, identity needed
only at covered address lists -- not wherever integrated). Even formal
sectors (wrong V predicate) contribute only zeros; no need to explicitly
switch C on those, nor require gap in their forbidden placements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian Rows
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Wisps Tier Schur LocalJet
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (x : ℝ)
  (V : Config G c) (k : S.Choices) (J : ChartRatio G) {w d : ℝ}

/-- Includes actual enrollment of the *frozen* increments when read
on a selected potential stencil, physical Y cast. Not asking Y to pass
when substituted off other cutoffs, or at placed group supports not on
these affine stencils. -/
def Admitted (D : Allocation G S x w) (d : ℝ) := ∀ u : F.Slice G,
    D.bill A k (F.drape u) V ≠ 0 → Alive S (F.drape u) k →
    ∀ e : F.Free, (¬chill A x F e ∨ ∃ (s : Signed) (i : Where S), curb (shots S x) A F x s i ∧ e.val∈shots S x s i) →
      let y := replica S.ratio V e.val
      let l := u e * y⁻¹
      ∃ a : G.Color, ‖a‖ ≤ d ∧ a∈ball 0 J.radius ∧ a∈firstBall G ∧ G.lieExp a * y = u e ∧
        ∀ q : Chi, patched q d l = a

/-- Post-L anchor price. -/
theorem matinee (P : Teller G) (J : ChartRatio G) (hJ : LocalRatio J) (L : Side) (w : ℝ) (hw : 0<w) :
    ∃ D E : ℝ, 0<D ∧ 0<E ∧ ∀ᶠ x : ℝ in atTop,
      let d := D*fiery G x L
      0<d ∧ 4*d<J.radius ∧ 2*d<firstRadius G ∧ (∀ a : G.Color, ‖a‖≤4*d → |Real.log (J.J a)| ≤ E*‖a‖^2) ∧
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch.L=L →
      P.Funds S T → 100*(1+radiusB x) ≤ c.val → span S.patch x ≤ radiusB x/50 →
      ∀ (A : Stores S) (F : Forest S.ratio) (C : Allocation G S x w) (V : Config G c) (k : S.Choices),
        Admitted A F x V k J C d := by
  obtain ⟨E,r,hE,hr,hs,he⟩ := ratio_price hJ
  obtain ⟨C,δ,hC,hδ,hl⟩ := Next.Fluctuations.log_chart_cost G
  obtain ⟨c,hc,h⟩ := Work.E02.answer G L P.j P.bind
  let M : ℝ := ((box ((P.j+7)*L.val)).card : ℝ)*Fintype.card PlaqAxes
  let m := c*M+2*w
  have hm : 0<m := add_pos_of_nonneg_of_pos (mul_nonneg hc.le (by unfold M; positivity)) (by positivity)
  let D := C*m
  have hd : 0<D := mul_pos hC hm
  refine ⟨D,E,hd,hE,?_⟩
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop ((P.j+7)*L.val+P.j+8),
    Work.E01.fiery_le G L (4*D), Work.E01.fiery_le G L m,
    (Work.E01.betaF_tendsto G L).eventually (eventually_gt_atTop 0),
    (Work.E01.largeT_tendsto G L).eventually (gt_mem_nhds (lt_min (lt_min hr hδ) (first_pos G)))] with x hx ha ht hp hU
  have hn : 0 < fiery G x L := Work.E09.temp_pos (x:=betaF G x L) hp
  intro d
  have hf : 0<d := mul_pos hd hn
  have hβ : largeT G x L < r := lt_of_lt_of_le hU (le_trans (min_le_left ..) (min_le_left ..))
  have hα : largeT G x L < firstRadius G := lt_of_lt_of_le hU (min_le_right ..)
  have hχ : largeT G x L ≤ δ := hU.le.trans (le_trans (min_le_left ..) (min_le_right ..))
  have hj : 4*d < r := by unfold d; linarith
  have hz : 2*d < firstRadius G := by unfold d at *; linarith
  refine ⟨hf,hj.trans hs,hz, fun a hy => (he _ (hy.trans hj.le)).2.2,?_⟩
  intro c' f S T hL hT hF hb A F π V k a hA hAa e hh ν Y
  let U := F.drape a; let i := S.ratio.parent e.val.1
  have hg : S.patch.J=P.j := hT.atStep
  have hu : 100*macroR S.patch ≤ f.val := by
    have hh : c'.val ≤ f.val := by rw [S.sizes]; exact le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property
    rw [Work.E01.macroR_eq,hL,hg]; omega
  have help := h c' f S hT.knobs hL hg hu (by omega) F U (fun i hi => F.on_tree a ⟨i,hi⟩)
    V e.val k (wraps S k hAa _)
  have hk : i ∉ A.dome (9*radiusB x+8*radiusB x/10) := by
    obtain h | ⟨s,y,hv,he⟩ := hh
    · intro he
      obtain ⟨t,ht,hu⟩ := halo_spec.mp he
      apply h; exact Or.inl (halo_spec.mpr ⟨t,ht,by change separation t i ≤ _; omega⟩)
    exact ((guarded hb hv).2 _ he).1
  have hQ := π.actual _ _ _ _ hA
  let t := fiery G x L
  have hports : port S i U ≤ M*t := by
    have hi (p : Cell f) (h : 0 < mcharge S i p) : toll U p ≤ fiery G x S.patch.L := by
      have hb : p ∉ A.costs := by
        intro hl
        have hp := Work.E01.mcharge_maps S i p h
        apply hk
        refine halo_spec.mpr ⟨S.ratio.parent p.1, ?_,(separation_comm ..).trans_le (hp.trans (by omega))⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p,hl,Finset.mem_image_of_mem _ (Work.E01.base_touched _)⟩))
      exact ((hQ.fine p).2 hb).trans (by have := temp_nonneg (betaF G x S.patch.L); unfold fiery; linarith)
    have hr := Work.E01.port_le S U i (fiery G x S.patch.L) (temp_nonneg _) hi
    rwa [Work.E01.macroR_eq,hL,hg] at hr
  have hwire : wire (S.prediction U k) V (i,e.val.2) ≤ 2*w*t := by
    unfold t; rw [← hL]
    refine ((hQ.coarse _).2 fun hi => hk ?_)
    exact halo_subset _ _ ((Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(i,e.val.2),hi,by simp [pinPos]⟩))) : i∈A.place)
  have hv : G.chord Y ≤ m*t := by
    dsimp only [Cops] at help; rw [show U e.val=a e from F.off_tree a _] at help
    refine help.trans ((add_le_add (mul_le_mul_of_nonneg_left hports hc.le) (show (if _ then _ else wire _ _ _) ≤ 2*w*t from ?_)).trans_eq (by unfold m; ring))
    split
    · exact mul_nonneg (by positivity) hn.le
    exact hwire
  obtain ⟨h',h1⟩ := hl Y (hv.trans (ht.trans hχ))
  set a' := G.plog (G.mat Y)
  have hh : d<firstRadius G := by linarith
  have hv' : G.lieExp a' * ν = a e := by rw [h']; unfold Y; simp
  have h₀ : ‖a'‖ ≤ d := h1.trans ((mul_le_mul_of_nonneg_left hv hC.le).trans (le_of_eq (mul_assoc C m _).symm))
  refine ⟨a',h₀,mem_ball.mpr (by rw [dist_zero_right]; linarith),mem_ball.mpr (by rw [dist_zero_right]; linarith),hv',?_⟩
  intro q
  rw [← show G.lieExp a'=Y from h', patched_agrees q hf hh h₀]

/-- When V predicates are misrecorded, no need to assemble possibly
singular C. Even if reading the same everywhere-defined formulas, bills
stay identically zero and we give L¹ and equality on those cells too. -/
theorem displaced_wrong {d w : ℝ} (D : Allocation G S x w) (q : Chi) (R : Rep G f) (W : Stencils S)
    (C : Gaussian.Table (In x A F (G:=G))) (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (h : A.flags≠RG.flags (temp x) V) : Licenses T x V k A R W F D q J d C m := by
  have he (U : Config G f) : D.bill A k U V = 0 := not_not.mp fun hx => h (D.actual _ _ _ _ hx).exactFlags
  let g := dyed T x V k A R W F D q J d C m
  have hg : g = 0 := by funext y z; unfold g dyed; simp [he]
  let t := D.portion A F V (fun k a => exposed R (till x) (F.drape a) * enters T R.beta x k V (F.drape a)) k
  have ht : t = 0 := by funext y; unfold t Allocation.portion; simp [he]
  constructor
  · change Integrable t _; rw [ht]; exact integrable_zero ..
  · intro Y; change Integrable (g Y) _; rw [hg]; exact integrable_zero ..
  · change Integrable (uncurry g) _; rw [hg]; exact integrable_zero ..
  change (∫ a,t a ∂_) = _ * ∫ y,(∫ z,g y z∂_)∂_
  rw [ht,hg]; simp

lemma sponsored_permit (P : Teller G) (Z : ChartRatio G) (hZ : LocalRatio Z)
    (Q : Patch) (hB : Q.Branches P.bind G) (w : ℝ) (hw : 0<w) :
    ∃ C E : ℝ, 0<C ∧ 0<E ∧ ∀ᶠ x : ℝ in atTop,
    let d := C*fiery G x Q.L
    (∀ a : G.Color, ‖a‖ ≤ 4*d → |Real.log (Z.J a)| ≤ E*‖a‖^2) ∧ 0 < d ∧ 2*d<firstRadius G ∧ 4*d < Z.radius ∧
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=Q → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
    100*macroR S.patch ≤ f.val ∧ 1<c.val ∧ ∀ (A : Stores S) (F : Forest S.ratio) (k:S.Choices) (V : Config G c) (B : Allocation G S x w) (q : Chi),
    Admitted A F x V k Z B d ∧ (A.flags=RG.flags (temp x) V →
      ∀ β : ℝ, 0<β → Permitted x V k A F B Z d β (fog A F T x V k) (meanLog A F T x V k q d) ∧
      (Rows.gram T x V k (shots S x) A F).PosDef ∧ (∃ B, 0 < B ∧ Authorized A V F x B)) := by
  obtain ⟨C,E,h,H,h1⟩ := matinee P Z hZ Q.L w hw
  obtain ⟨v,K,η,b,E',-, -, -, -, -,h2⟩ := opaqueCost G Q P hB
  refine ⟨C,E,h,H,?_⟩
  obtain ⟨β,δ,hβ,hδ,he'⟩ := earned Q P.bind G hB
  have hm : ∀ᶠ x : ℝ in atTop, permit Q*temp x≤δ := by
    filter_upwards [Work.E01.fiery_le G (1:Side) (permit Q), (Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hδ)] with x hx he
    simpa [fiery,betaF] using hx.trans he
  filter_upwards [h1,h2, Work.E01.radiusB_tendsto.eventually_ge_atTop (macroR Q+allot Q+1),small_span Q,hm] with x hx hv hα hσ hAuth
  intro d
  obtain ⟨he,hg,ht,hl,hh⟩ := hx
  refine ⟨hl,he,ht,hg,fun c f S T hs hc hP => ⟨?_,by omega,?_⟩⟩
  · have hh : c.val ≤ f.val := by rw [S.sizes]; exact le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property
    rw [hs]; omega
  intro A F k V B q
  have hi := hh S T (congr_arg RG.Patch.L hs) hP hc (by rw [hs]; exact hσ) A F B V k
  refine ⟨hi,fun hy _ hβR => ?_⟩
  obtain ⟨-,-,hr,-,hz⟩ := hv S T hs hc hP A F k V hy
  refine ⟨⟨hz,hβR,(meanLog_cont _ _ _ _ _ _ _ _ hP he ht).measurable,fun u hu hf i => ?_,hZ,he,hg⟩,hr,β,hβ,he' S hs hP.knobs F A V x hy hσ (by omega) (by omega) hAuth⟩
  obtain ⟨a,ha,hx,-,hc,-⟩ := hi u hu hf i.val (Or.inl i.property)
  exact ⟨a,ha,hx,hc⟩
end YM.Next.SectorChange
