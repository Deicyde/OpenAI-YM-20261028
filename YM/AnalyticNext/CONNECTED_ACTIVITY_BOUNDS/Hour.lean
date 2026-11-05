import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Breath

/-!
# Sharp plateau tests. Where pre-L is needed

C0. Includes α-likelihood letters even on actual transformed charts where
only that site/bond's Z neighborhood is guarded. Not asserting eligibility
at other off-window places. Strict chord margin bought for defaults;
increase W after issue along WITH the `Buy` exponential, don't raise it
on an old `PointCharge`. E δ tests thus at authentic rollout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Jewels
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint  Wages
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

-- pre-L bound C; same everywhere else
def slew (P : Teller G) := Real.sqrt P.top.clip.direct /64
lemma slew_pos (P : Teller G) : 0<slew P := div_pos (Real.sqrt_pos.mpr P.top.clip.quadratic_pos) (by norm_num)

def wedge (P : Teller G) (C : ℝ) (L : Side) := C/(L.val:ℝ)^2 ≤ slew P
def Wedge (P : Teller G) (C W : ℝ) := C + slew P ≤ (W/4)*Real.sqrt P.bind.penalty

lemma pre (P : Teller G) (C : ℝ) : ∃ N : ℕ, ∀ L : Side, N ≤ L.val → wedge P C L := by
  let f (i : ℕ) := (i:ℝ)^2
  have he : Tendsto f atTop atTop := ((tendsto_pow_atTop (n:=2) (by norm_num)).comp tendsto_natCast_atTop_atTop)
  have hp := eventually_atTop.mp (he.eventually_ge_atTop (C / slew P))
  obtain ⟨N,h⟩ := hp
  refine ⟨N,fun L hL => (div_le_iff₀ (show 0<(L.val:ℝ)^2 from pow_pos (side_pos L) _)).mpr ?_⟩
  rw [mul_comm]; exact (div_le_iff₀ (slew_pos P)).mp (h L.val hL)

lemma settlers (P : Teller G) (C : ℝ) : ∀ᶠ W in atTop,Wedge P C W := by
  have hp := Real.sqrt_pos.mpr P.bind.penalty_pos; let s := Real.sqrt P.bind.penalty
  filter_upwards [eventually_ge_atTop (4*(C+slew P)/s)] with W hW
  unfold Wedge; change _≤W/4*s; linarith only [(div_le_iff₀ hp).mp hW]

lemma edge_choice (k : S.Choices) (U : Config G f) (h : S.patch.Branches S.kernel G) : S.prediction U (choice 1 k) = S.prediction U k := by
  simpa only [pull_id] using (carry 1 h k U).2

-- literal over all probes; no multiplicity. Arrays z in raw scaled form.
structure Keys (W ε x : ℝ) (C : ℝ) (P : Teller G) (D : Patch) (X : Turns) : Prop where
  fits : Reserve P C
  earns (c f : Side) (S : StepData c f) (T : Tube G S) : S.patch=D → P.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (Y : Mint T F A x), cert S x A Y.V → ∀ J K, Alongside J K T →
    X.Takes (eyes S G (radiusB x)) Y.sheet (dcol S) (paceR x) → Y.u=holdSize G D x →
    ∀ z : ArrayR G f, let U := Y.build (Y.μ+z); let B := radiusB x; let t := fiery G x S.patch.L
    (∀ i : Cell f, let p := S.ratio.parent i.1; p∉ A.dome (20*B) → Awake S B p z (ε*t) →
      toll U i < t/4) ∧ ∀ i : Bond c,i.1∉ A.dome (20*B) → Awake S B i.1 z (ε*t) →
        wire (S.prediction U Y.k) Y.V i < W*t ∧ αSite U i.1 Y.k=1 ∧ αBond U i Y.k=1

theorem night (P : Teller G) (C : ℝ) (hc : Reserve P C) (D : Patch) (hd : D.Branches P.bind G)
    (he : wedge P C D.L) (W : ℝ) (hp : 0<W) (hW : Wedge P C W) (X : Turns) : ∃ ε : ℝ, 0<ε ∧
    ∀ᶠ x in atTop, Keys W ε x C P D X := by
  obtain ⟨K,u,hK,hu,h⟩ := Work.E05.curvature_lower G
  obtain ⟨ε,hs,hε⟩ := guard_δ P C hc D hd X (slew P) (slew_pos P)
  refine ⟨ε,hs,?_⟩
  filter_upwards [hε,hc.receipt D.L,pos_size G D, guard_stops P C hc D hd ε hs.le X,
    shine G D 17 (by norm_num), (vanishes G D (17+2+1)).eventually (eventually_lt_nhds hu),
    face_pays G D (17+2), cordF D P.bind hd (17+2) u hu] with x hx hp' hu hs hh hg hc' hQ
  refine ⟨hc,?_⟩
  intro c f S T hS hT A F Y hY J K hK hr hb z U B t
  have ht : 0<t := by unfold t; rw [hS]; exact hu.1
  have hy i (he : i∉ A.dome (20*B)) (h : Awake S B i z (ε*t)) : ∃ y, Lit S Y.V U i (B/2) (allowance G D x 1 (17+2)) y := by
    have hc := (hs _ _ S T hT hS A F Y hY hr hb z i he (congr_arg (fun L => Awake S B i z (ε*fiery G x L.L)) hS ▸ h))
    simpa only [pull_id] using hh _ _ S U Y.V A _ hS hY 1 i (fun hi => he (placed A _ _ (by omega) hi)) hc
  have hM := (hp' c f S T hT (congr_arg Patch.L hS) hY.1 F Y.V).2.2
  have hz (H : G.El) (he : G.chord H ≤ u) : G.chord H ≤ 2*‖G.curvature H‖ := by
    nlinarith only [(h _ he).2,G.chord_nonneg H,norm_nonneg (G.curvature H)]
  have hF p (hi : base S p∉ A.dome (20*B)) (h : Awake S B (base S p) z (ε*t)) :
      ‖target T (till x) (temp x) p Y.k Y.V U‖ ≤ slew P*t := by
    apply (hx _ _ S T hT hS A F Y hY J K hK hr hb p z hi _).trans
    · unfold t; rw [hS]
    rw [← hS]; exact h
  let v := T.vision (till x) (temp x) Y.V
  let a := Real.sqrt P.top.clip.direct; have ha : 0 < a := Real.sqrt_pos.mpr P.top.clip.quadratic_pos
  constructor
  · intro j i he' ht'
    let u := T.Xf (till x) U (j,false); let y := T.Mv (till x) (temp x) Y.V (j,false)
    have hh : ‖u-y‖ ≤ slew P*t := by
      have hi := hF (straightF S j) he' ht'
      rwa [target,show (straightF S j).1 = 1 from rfl,pull_id,pull_id] at hi
    have hD : ‖y‖ ≤ slew P*t := (hM.phi _).trans (mul_le_mul_of_nonneg_right (show C/(S.patch.L.val:ℝ)^2≤_ from
      by rw [hS]; exact he) ht.le)
    have hk : ‖G.curvature (faceValue U j)‖ ≤ t/32 := by
      apply le_of_mul_le_mul_left _ ha
      have hc : ‖u‖ = a*‖G.curvature (faceValue U j)‖ := by
        unfold u Tube.Xf; rw [hT.high,plotted,if_neg (by simp),shoot,norm_smul,Real.norm_of_nonneg ha.le]
      calc
        _ = _ := hc.symm
        _ ≤ _ := (norm_le_norm_sub_add u y).trans ((add_le_add hh hD).trans_eq (by unfold slew a; ring))
    obtain ⟨g,hg'⟩ := hy i he' ht'
    apply (hz (faceValue U j) ((hc' S j _ _ _ hg').trans hg.le)).trans_lt; linarith
  intro i hi hh
  obtain ⟨g,hg⟩ := hy i.1 hi hh
  obtain ⟨hy,hg,hc⟩ := hQ S i Y.V U g Y.k hS hT.knobs hg
  refine ⟨?_,hg,hc⟩
  let u := Y.V i * (S.prediction U Y.k i)⁻¹
  let L := Real.sqrt P.bind.penalty; have hl : 0<L := Real.sqrt_pos.mpr P.bind.penalty_pos
  let y := T.Mw (till x) (temp x) Y.V i; let v := Tube.Z S (S.prediction U Y.k) Y.V i
  have hm : ‖v-y‖ ≤ slew P*t := by
    have hv := hF (straightI S i) hi hh
    rw [target,show (straightI S i).1 = 1 from rfl,pull_id,pull_id,edge_choice _ U (funds_branch hT)] at hv
    exact hv
  -- shadow `hm`; fix name
  have hc : ‖v‖=L*‖G.curvature u‖ := by unfold v Tube.Z; rw [norm_smul,hT.knobs,Real.norm_of_nonneg hl.le]
  have he : ‖G.curvature u‖≤W*t/4 := by
    apply le_of_mul_le_mul_left _ hl
    rw [← hc]
    apply le_trans (norm_le_norm_sub_add v y)
    have ht'' := mul_le_mul_of_nonneg_right hW ht.le
    linarith only [hm, show ‖y‖ ≤ C*t from hM.hot _, show (C+slew P)*t ≤ _ from ht''] -- ensure arithmetic order
  apply lt_of_le_of_lt (hz u hy.le); linarith only [he,mul_pos hp ht]
end YM.AnalyticNext.ConnectedActivity.Jewels
