import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Accuracy
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.MinBranches


/-!
# Physical patch caps, touched threshold and color coordinates

Including V arbitrary off the numerical hull. For small-chart predictor,
mean+noise assertion on true Q choices from the same U (even likelihood in
probability convention at those physical addresses, not assuming positivity
on incoming path points). Exponential gains are spent later.
-/

set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations Work.E03
open Bloch Laurent
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {L : Side} {c f n : Side} {S : StepData c f} {T : Tube G S}

/-- One weak chart receipt (tower conditional). Covers U and V in the SAME local gauge.
Keep h separate from φ B costs, can also cost contours later, need own proofs there. -/
structure Blanket (S : StepData c f) (U : Config G f) (V : Config G c) (i : Site c) (d : ℕ)
    (g : Site c → G.El) (b : LogField G c) (h : ℝ) : Prop where
  reaches : AgreeNear id i d (gauge g V) (represent b)
  bound : ‖b‖ ≤ h
  coarse (j : Bond c) : separation i j.1 ≤ d → G.chord (gauge g V j) ≤ h
  fine (j : Bond f) : distAt S j i ≤ d → G.chord (gauge (constantGauge g S.ratio) U j) ≤ h

lemma layered (P : Teller G) (L : Side) {H : ℝ → ℝ} (h : Rate G L (-(1/2)) H) (hp : ∀ᶠ x in atTop,0 ≤ H x) :
    ∃ W, Rate G L (-(1/2)) W ∧ ∀ᶠ x : ℝ in atTop,
    H x ≤ W x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → Room P S T x →
    ∀ (V : Config G c) (U : Config G f) (i : Site c) (d : ℕ), d ≤ 32*radiusB x → Clean V x i (d+1) →
      ∀ u : Directions G f, Grafted V U u i d (H x) S → ∃ g b, Blanket S U V i d g b (W x) := by
  obtain ⟨v,hv,hf⟩ := flattening P L
  obtain ⟨D,r,hD,hr,H₂⟩ := chord_chart_cost G
  let J x := H x + v x
  let W x := J x + (D*H x+D*v x)
  refine ⟨W,(h.add hv).add ((h.mul_left D).add (hv.mul_left D)),?_⟩
  filter_upwards [hp,h.below (by norm_num) r hr,hf,hv.below (by norm_num) r hr] with x ht hh he hk
  obtain ⟨hx,he⟩ := he
  have hs : 0 ≤ J x := by unfold J; positivity
  have hc : 0 ≤ D*v x := by positivity
  have ho : 0 ≤ D*H x := by positivity
  refine ⟨(by unfold W J; linarith),?_⟩
  intro c f S T hL hR V U i d hd hi u hh'
  obtain ⟨g,b,hm,hy⟩ := he c f S T hL hR V i d hd hi
  have hv (j : Bond c) (hp : separation i j.1 ≤ d) :
      G.chord (gauge g V j) ≤ D*v x := by
    have hi : ‖b (pole j)‖ ≤ v x := (norm_le_pi_norm _ _).trans hy
    rw [hm j hp,Work.F03.represent_link]
    exact (H₂ _ ((hi.trans (le_abs_self _)).trans hk)).trans (mul_le_mul_of_nonneg_left hi hD.le)
  have hw : D*v x ≤ W x := le_trans (le_add_of_nonneg_left ho) (le_add_of_nonneg_left hs)
  refine ⟨g,b,hm,hy.trans (by unfold W J; linarith),fun j hp => (hv j hp).trans hw,?_⟩
  intro j hp
  have hu := hh'.spin g
  have he := hu.norm j hp
  have hv' : G.chord (replica S.ratio (gauge g V) j) ≤ D*v x := by
    unfold replica; split
    next => rw [G.chord_one]; exact hc
    exact hv _ hp
  rw [hu.read j hp,increment]
  exact (G.chord_triangle ..).trans ((add_le_add ((H₂ _ ((he.trans (le_abs_self _)).trans hh)).trans
    (mul_le_mul_of_nonneg_left he hD.le)) hv').trans (le_add_of_nonneg_left hs))

lemma strokes (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) {w : ℝ → ℝ}
    (h : Rate G L (-(1/2)) w) (hp : ∀ᶠ x in atTop, 0 ≤ w x) :
    ∃ M E, Rate G L (-(1/2)) M ∧ Rate G L (-1) E ∧
    ∀ᶠ x : ℝ in atTop, 0 ≤ M x ∧ 0 ≤ E x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D →
    S.patch.L=L → Room P S T x → ∀ (U : Config G f) (k : S.Choices) (V : Config G c) (p : Rod c f) (u : Directions G f),
      let i := focus S p; let d := radiusB x; let R := till x
      Clean V x i d → Grafted V U u i (d/2) (w x) S →
        let C := entryCost T R U k V p; let Y := baseStroke T x k V p
        ‖C‖ ≤ M x ∧ ‖C-(Y + straightened T R V u p)‖ ≤ E x := by
  obtain ⟨W,H,hW⟩ := layered P L h hp
  obtain ⟨M,E,hM,hE,h⟩ := within P L D hD H ((hp.and hW).mono fun _ he => he.1.trans he.2.1)
  refine ⟨M,E,hM,hE,?_⟩
  filter_upwards [h,hW] with x he hw
  refine ⟨he.1,he.2.1,?_⟩; intro c f S T hS hL hr U k V p u i d R hV hU
  have h1 : 100 ≤ d := hr.sight.1
  obtain ⟨g,b,H⟩ := hw.2 c f S T hL hr V U i (d/2) (by unfold d; omega)
    (hV.shrink (v:=i) (by rw [separation_self]; omega)) u hU
  let z := constantGauge g S.ratio
  have hy := he.2.2 c f S T hS hr b (gauge g V) (gauge z U) (spinRow S g u) k p H.bound
    (H.reaches.shrink (by change separation i i + d/4 ≤ _; rw [separation_self]; omega))
    (((hU.spin g).less (i:=i) (d:=d/4) (by rw [separation_self,zero_add]; omega)).raise hw.1)
  dsimp only at hy
  obtain ⟨hl,hS',h₃⟩ := hy
  intro C Y
  obtain ⟨a,e,hh,-⟩ := hr.accepted.feeds
  have hk (W k) := entry_turn hr.accepted R W k V g p
  unfold z at *; rw [hk,G.norm_adjoint] at hl
  refine ⟨hl,?_⟩
  rw [under T hh] at hS'
  unfold baseStroke at hS'
  rw [hk,← copied S.ratio S.patch.odd_side V g,hk,← map_add,← map_sub,G.norm_adjoint] at hS'
  exact hS'

lemma tags_at (h : P.Funds S T) (z : Site c → G.El) (U : Config G f) (k : S.Choices) (V : Config G c) (b : Bond c) :
    let t:=constantGauge z S.ratio; let U':=gauge t U; let V':=gauge z V
    Tags.siteMass U k b.1=Tags.siteMass U' k b.1 ∧ Tags.pinMass U k b=Tags.pinMass U' k b ∧
      wire (S.prediction U k) V b=wire (S.prediction U' k) V' b := by
  intro t U' V'; have he := SectorMeasure.funds_branch h
  constructor
  · unfold U' Tags.siteMass; rw [expandAt_gauge]; exact congr_arg _ (S.patch.frame_gauged he ..).1.symm
  constructor
  · unfold U' Tags.pinMass; rw [StepData.updateGauged S he]; exact congr_arg _ (S.patch.bond_gauge (h:=he) ..).1.symm
  unfold U' V'; rw [(SectorMeasure.choice_gauge he U k t).2]
  rw [show t ∘ S.ratio.embed=z from funext fun i => congr_arg z (S.ratio.embed_parent i)]; exact (SectorMeasure.wire_gauge ..).symm

/-- Read the actual tags even before broad guards restored. Sufficiently
weak at every particular post-L δ. -/
lemma marks_here (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) {w : ℝ → ℝ}
    (h : Rate G L (-(1/2)) w) (hp : ∀ᶠ x in atTop, 0 ≤ w x) (δ : ℝ) (ht : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D →
    S.patch.L=L → Room P S T x → ∀ (U : Config G f) (k : S.Choices) (V : Config G c) (i : Site c) (u : Directions G f),
      let d := radiusB x
      Clean V x i d → Grafted V U u i (d/2) (w x) S →
        Tags.siteMass U k i = 1 ∧ (∀ a : Axis, Tags.pinMass U k (i,a)=1 ∧ wire (S.prediction U k) V (i,a) ≤ δ) ∧
        ∀ (p : Cell f), i=S.ratio.parent p.1 → toll U p ≤ δ := by
  obtain ⟨W,H,hW⟩ := layered P L h hp
  obtain ⟨r,k',hr,hk⟩ := Forward.approves D P.bind hD (δ:=δ/2) (by linarith)
  filter_upwards [H.below (by norm_num) (min r (δ/4)) (lt_min hr (by linarith)),hW,hp,
    Work.E08.eventual_radiusB (2*k'+12)] with x hx hw h' hx' c f S T hS hL hR U k V i u B hV hU
  have h₀ : 100 ≤ B := hR.sight.1
  have hy : k' ≤ B/2 := by unfold B; omega
  have hp : 0 ≤ W x := h'.trans hw.1
  obtain ⟨hv',hi⟩ := le_min_iff.mp ((le_abs_self _).trans hx)
  obtain ⟨g,b,H⟩ := hw.2 c f S T hL hR V U i (B/2) (by unfold B; omega)
    (hV.shrink (v:=i) (by rw [separation_self]; omega)) u hU
  let U':=gauge (constantGauge g S.ratio) U
  let V':=gauge g V
  obtain ⟨he,hb⟩ := hk c f S hS hR.accepted.knobs U' k i (fun j hj => (H.fine j (hj.trans hy)).trans hv')
  have hz (a : Axis) := tags_at hR.accepted g U k V (i,a)
  refine ⟨(hz 0).1.trans he,fun a => ⟨(hz a).2.1.trans (hb a).2,?_⟩,?_⟩
  · refine le_trans (hz a).2.2.le ?_
    unfold wire; apply (G.chord_triangle ..).trans
    rw [G.chord_inv]; exact (add_le_add (H.coarse _ (by simp)) (hb a).1).trans (by linarith)
  intro p he
  let Z' (b : Bond f) := if distAt S b i ≤ B/2 then U' b else 1
  have hl : faceValue U' p=faceValue Z' p := by
    refine (travel_near S.ratio.parent (parent_step S) _ _ _ _ (B/2) (show 4 ≤ B/2 by omega) ?_)
    intro j hj; rw [← he] at hj; exact Eq.symm (if_pos hj)
  have hu j : G.chord (Z' j) ≤ W x := by unfold Z'; split <;> first | rwa [G.chord_one] | exact H.fine _ (by assumption)
  unfold toll
  rw [← show G.chord (faceValue U' p) = G.chord (faceValue U p) from SectorMeasure.toll_gauge (constantGauge g S.ratio) U p,hl]
  refine le_trans (travel_chord Z' _ _ (W x) hu) ?_
  change (↑(4:ℕ):ℝ)*W x ≤ δ
  push_cast; linarith
end YM.ConnectedActivityE6.SliceRows
