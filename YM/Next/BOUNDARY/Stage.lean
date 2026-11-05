import YM.Integrated
import YM.Next.BOUNDARY.Core
import YM.Next.BOUNDARY.Unique
import YM.Org.Theatre
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04
import YM.Work.B06



/-!
# Continuation over the producer interfaces

Further compatibility at RStage. Do not condition on the existence of the
field model. The C-chain can also produce fields for **both** S and T,
from the specified Euclidean data, without switching contours when assembling
field models or forgoing conclusions on the one without UniqueHeat. It works
even when a (possibly independently constructed) `Contour.From` is
prescribed; upgrade its very waves (at all strict times) and its surface.
Attachments into the same OS chamber from *any* realizing field models.
At the end, run with both the unselected and retaining phase data. All
calibrations on the SAME Union.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY

open Set Filter Function MeasureTheory
open Boundary OS Spec Org
open scoped Topology InnerProductSpace NNReal ENNReal

variable {G : Gauge} {C : Family G} {S T : Table C.book} {V : Chamber T timeAxis}
variable {P : DiffPlan S} {X : Algebra S} {K : Spins S} {J : StarOp S}
variable {A : Spread V} {Y : Show.Rhythm (C:=C) S V A} {W : Surface S}
variable {B : Contour S}

theorem rhythm (H : Bid.Pantry S T V P A) : Nonempty (Show.Rhythm (C:=C) S V A) := by
  obtain ⟨B, hB⟩ := Integrated.reconstructionArcs.cA S T V P A H
  obtain ⟨F, hF⟩ := Integrated.reconstructionArcs.cC S T V A B
    (Integrated.reconstructionArcs.cB S T V P A B H hB)
  obtain ⟨hx, hu, hq⟩ := Integrated.reconstructionArcs.cD S T F hF.reach hF.birth
  exact ⟨B, hB.bits, hB.price, F, hF.tune, hF.reach, ⟨hF.birth,hx⟩, hq, hu⟩

theorem contour (H : Bid.Pantry S T V P A) : ∃ B : Contour S, B.From T := by
  obtain ⟨Y⟩ := rhythm H
  obtain ⟨U, -, hx⟩ := Y.opens
  exact ⟨_, hx⟩

/-- Strengthening of contour existence: Preserves the chosen B. -/
theorem at_contour (H : Bid.Pantry S T V P A) (hb : B.From T) :
    B.waves.NonTangentialFree B.world ∧ ∃ Y : Show.Rhythm (C:=C) S V A, Y.lift=B.waves := by
  have hs := H.head.laws.toSymmetric
  obtain ⟨r⟩ := rhythm H
  have ht n x z (hz : z∈strict n) := waves_eq hb.heat r.birth P hs H.rises n x z hz
  have hY : B.waves.Breathes := by
    intro n v
    obtain ⟨m,c,hc,hM⟩ := r.power.1 n v
    refine ⟨m, c, hc, fun y k hk h x => ?_⟩
    have hy : y∈east n := fun i j hij => sub_pos.mp (lt_of_lt_of_le hk.1 (h i j hij))
    have he : shift x y ∈ strict n := by
      intro i j hij
      simpa [shift] using hy hij
    unfold Waves.restricted
    rw [ht n _ _ he]
    exact hM y k hk h x
  have hD : r.bits.Defined B.waves := by
    intro n z h p ht' x v
    rw [ht n x z h]
    exact r.yields n z h p ht' x v
  obtain ⟨hv, hh, hm⟩ := Integrated.reconstructionArcs.cD S T B.waves hb.heat hY
  let Y : Show.Rhythm (C:=C) S V A :=
    ⟨r.bits, r.linked, r.price, B.waves, hD, hb.heat, ⟨hY, hv⟩, hm, hh⟩
  obtain ⟨U,H',hq⟩ := Y.opens
  refine ⟨?_, Y, rfl⟩
  rw [surface_eq hb hq P hs H.rises]
  exact H'

section scenery

theorem illuminated (H : Bid.Pantry S T V X.derivatives A) (y : Show.Rhythm (C:=C) S V A)
    (h : y.lift.NonTangentialFree W) (hx : X.turns.Oriented T) (hX : X.turns.Laws X.derivatives H.head.spin)
    (hk : K.Descends X.turns H.head.spin) : Show.Lights S K y W := by
  have e := Integrated.reconstructionArcs.cG S T X.turns K H.head X.derivatives H.rises H.adopted
    H.present hx hX hk y.lift y.birth y.power.1 y.power.2 y.shore.1 y.shore.2
  have r := Integrated.reconstructionArcs.cI Work.A16.answer Integrated.reconstructionArcs.cH S T X.turns K
    H.head X.derivatives H.rises H.adopted H.present hx hX hk y.lift W y.birth y.power.1 e h
  have u := Integrated.reconstructionArcs.cE S T y.lift W y.birth y.power.1 y.shore.1 y.shore.2 h
  exact ⟨r, u, Integrated.reconstructionArcs.cF S T y.lift W y.birth y.power.1 y.power.2 u⟩

theorem spectra (I : Show.Lights (C:=C) S K Y W) : Bid.cones W := fun n => tents W K I.rotates (I.braces n)

lemma blankets (D : ∀ n, Blanket n) (i : ℕ) : (D i).Modified :=
  Integrated.reconstructionArcs.cL i (Integrated.reconstructionArcs.cJ i) (D i)

theorem visible (W : Surface S) (D : ∀ n, Blanket n) : Nonempty (W.Aurora D) := by
  obtain ⟨F, -⟩ := Integrated.reconstructionArcs.cM W D Integrated.reconstructionArcs.cJ (blankets D)
  exact ⟨F⟩

theorem neon_any (I : Show.Lights S K Y W) {D : ∀ n : ℕ, Blanket n} (F : W.Aurora D) : Show.Neon I F := by
  have c := spectra I
  obtain ⟨Z, he⟩ := Integrated.reconstructionArcs.cM W D Integrated.reconstructionArcs.cJ (blankets D)
  have hF (n : ℕ) (v : Fin n → S.Union) : AnalyticOnNhd ℂ (F.emit v) (tube n) := by
    intro x hx
    apply (he n v x hx).congr
    filter_upwards [(south n).mem_nhds hx] with x hx
    exact emit_eq W v (c n v) _ _ x hx
  exact ⟨blankets D, Integrated.reconstructionArcs.cO W D (blankets D) c F hF
    (Integrated.reconstructionArcs.cN W D (blankets D) c Integrated.reconstructionArcs.cJ F hF) Y.lift
    Y.birth Y.power.1 Y.power.2 I.axis⟩







/-- One sequence of spectator heights works through any aurora and all
labels over this C. Actually produce panes; with all pane choices sameGround
and Forms, hence the partial distributional exchange. -/
theorem windows (H : Bid.Pantry S T V X.derivatives A) (I : Show.Lights S K Y W)
    (hk : K.Descends X.turns H.head.spin) (n : ℕ) (P : NearPair n) :
    ∃ y : ℕ → Heights n, Tendsto (dawn ∘ y) atTop (𝓝 0) ∧
      ∀ m : ℕ, ∀ (D : ∀ n, Blanket n) (F : W.Aurora D) (v : Fin n → S.Union),
        Nonempty (P.Panes F v (y m)) ∧ ∀ E : P.Panes F v (y m), E.sameGround ∧ E.Forms := by
  obtain ⟨y,hy,hT⟩ := Integrated.reconstructionArcs.cQ n P
  refine ⟨y, hy, fun m D F v => ?_⟩
  obtain ⟨ha, hw⟩ := hT m
  obtain ⟨hD, hF⟩ := neon_any I F
  have h := spectra I
  have hs := H.head.laws.toSymmetric
  refine ⟨Integrated.reconstructionArcs.cS K W D Y.lift F h hF X.turns H.head.spin hk
    X.derivatives hs H.rises (Integrated.reconstructionArcs.cR _ _ _ hk)
    (Integrated.reconstructionArcs.cP W K D F Y.lift hD h I.rotates hF) n v P _ ha hw, fun E => ?_⟩
  exact ⟨Integrated.reconstructionArcs.cT X.derivatives Y.lift W D F hs H.rises
    H.adopted.laws.toSymmetric H.adopted.smooth H.present Y.birth hF _ v _ _ E,
    Integrated.reconstructionArcs.cU Y.lift W D F hD hF _ _ _ _ E⟩

/-- Use with or without a choice of character. Also return the
pre-Lamp Hull to use for all-heights Gram formulae. -/
theorem revealing (H : Bid.Pantry S T V X.derivatives A) (hr : X.derivatives.Orientation H.head.spin)
    (hx : X.turns.Oriented T) (hX : X.turns.Laws X.derivatives H.head.spin)
    (hk : K.Descends X.turns H.head.spin) (hj : starRead J H.head.spin)
    (hn : ∀ d, T.null d=S.null d) (Y : Show.Rhythm (C:=C) S V A)
    (hw : Y.lift.NonTangentialFree W) : Show.Reveals X K J Y W ∧ Bid.Hull Y.bits Y.lift J := by
  have ht : Bid.Piece A Y.bits := ⟨Y.linked, Y.price⟩
  have hD : Bid.Direct A Y.bits Y.lift :=
    ⟨Integrated.reconstructionArcs.cB _ _ _ _ _ _ H ht, Y.yields, Y.birth, Y.power.1⟩
  have hh := Integrated.reconstructionArcs.cV S T _ X.derivatives _ _ _ H J hj hD hr H.present
  have I := illuminated H Y hw hx hX hk
  refine ⟨⟨I, ?_, fun D F _ n v P => ?_, fun D F hF => Integrated.reconstructionArcs.cZ
    Integrated.reconstructionArcs.cY _ _ X.derivatives D W _ _ hn H.adopted H.head H.rises
    H.habits Y.birth hF.2, Integrated.reconstructionArcs.cX S T _ _ _ _ _ _ _ W H Y.birth hw
      (Integrated.reconstructionArcs.cW _ _ _ X.derivatives _ _ _ _ H ht hk) hh⟩, hh⟩
  · let D := fun i : ℕ => Classical.choice (Integrated.reconstructionArcs.cK i)
    let F := Classical.choice (visible W D)
    exact ⟨D, F, neon_any I F⟩
  obtain ⟨y, hy, ht⟩ := windows H I hk n P
  refine ⟨y, hy, fun m => ?_⟩
  obtain ⟨⟨E⟩, he⟩ := ht m D F v
  exact ⟨E, he E⟩
end scenery

/-- Without assuming only-with-heat invariant-vector uniqueness; otherwise
keep all the Realizes fields. Adapt the construction of Boundary.harvest. -/
theorem establishing (H : Bid.Pantry S T V X.derivatives A)
    (hk : K.Descends X.turns H.head.spin) (hj : starRead J H.head.spin)
    (hY : Show.Reveals X K J Y W) :
    ∃ F : Wightman S, F.J=J ∧ F.spin=K ∧ FieldCore W X.turns H.head.spin F := by
  obtain ⟨a, e⟩ := Show.uses hY
  obtain ⟨hu, hTm⟩ := Integrated.reconstructionArcs.cν Integrated.reconstructionArcs.cH _ W J
    _ _ X.derivatives H.head.spin H.head.laws.toSymmetric H.rises hk hj hY.I.rotates
  obtain ⟨p, hc⟩ := Integrated.reconstructionArcs.cε S W J
  have ht := Boundary.invol H.head.laws.toSymmetric H.rises hj
  have hx := Integrated.reconstructionArcs.cμ S W a
  let G := (Y.bits.bowls hY.water).out
  let Z := Classical.choice (Kernel.host G.safe)
  obtain ⟨L, hL⟩ := Soil.mobilize (show Soil W J from Z) K hk hTm hu
  obtain ⟨U, hw⟩ := G.daylight Z L hL
  exact ⟨{ operators := Soil.starter (W:=W) Z p, J := J, action := L, momentum := L.orbit.P,
           spin := K }, rfl, rfl,
    ⟨hj, hk, Soil.usable Z p hc (G.soak H.adopted.laws), Soil.sharp Z p, Soil.relishes Z p,
      Soil.regional Z p hx, Soil.sees Z p ht e, Soil.cultivates Z K L hL p, L.orbit.total, L.spectrum hw⟩⟩

/-- Additional compatibility above BOTH ordinary contours with exact label
space, including auxiliary requirements for inspecting local germs. `FieldCore`
on an unselected contour contains NO invariant-vector uniqueness -- prove that
clause of the full theory on the selected phase below. -/
structure Compatible (S : Table C.book) {T : Table C.book} {V : Chamber T timeAxis}
    (A : Spread V) (X : Algebra S) (K : Spins S) (h : S.RealSpin) (B : Contour S) : Prop where
  fromPhase : B.From T
  corner : B.waves.NonTangentialFree B.world
  reveals : ∃ Y : Show.Rhythm (C:=C) S V A, Y.lift=B.waves ∧ ∀ (J : StarOp S),
    starRead J h → Show.Reveals X K J Y B.world ∧ Bid.Hull Y.bits Y.lift J
  core : ∃ F : Wightman S, FieldCore B.world X.turns h F
  attachments (F : Wightman S) : FieldCore B.world X.turns h F →
    F.spin=K ∧ ∃! U : F.operators.H →L[ℂ] V.H, Attachment F V U

theorem compatible (H : Bid.Pantry S T V X.derivatives A) (hr : X.derivatives.Orientation H.head.spin)
    (hx : X.turns.Oriented T) (hX : X.turns.Laws X.derivatives H.head.spin)
    (hk : K.Descends X.turns H.head.spin) (hn : ∀ d, T.null d=S.null d) (hB : B.From T) :
    Compatible S A X K H.head.spin B := by
  have he := H.head.laws.toSymmetric
  obtain ⟨hu, Y, hY⟩ := at_contour H hB
  have hv (J : StarOp S) (hj : starRead J H.head.spin) :=
    revealing H hr hx hX hk hj hn Y (W:=B.world) (hY.symm ▸ hu)
  refine ⟨hB, hu, ⟨Y, hY, hv⟩, ?_, fun F h => ?_⟩
  · let J := X.derivatives.unionAdj he H.rises timeAxis H.head.spin hr
    have hj : starRead J H.head.spin := calibrate he H.rises _ hr
    obtain ⟨F, -, -, hf⟩ := establishing H hk hj (hv J hj).1
    exact ⟨F, hf⟩
  obtain ⟨hp, hw⟩ := hv F.J h.induced
  have hh := spins_eq h.letters hk X.derivatives he H.rises
  exact ⟨hh, h.attach X.derivatives he H.rises Y.linked (hY.symm ▸ hu) hw (hh.symm ▸ hp.water)⟩

theorem Compatible.vacuum {h : S.RealSpin} (u : Compatible S A X K h B) (hv : V.UniqueHeat) :
    ∃ F : Wightman S, F.Realizes (W:=B.world) X.turns h ∧ F.spin=K := by
  obtain ⟨F, h⟩ := u.core
  obtain ⟨hF, U, hw, -⟩ := u.attachments F h
  exact ⟨F, hw.with_heat h hv, hF⟩

section both

variable {f : Extraction.Order} {s : Seed C f S} {α : Selection S}

theorem unselected_pantry (h : Materializes X α s.kernel.spin) :
    Bid.Pantry S S α.room X.derivatives α.unselected :=
  ⟨s.kernel, s.kernel, fun _ => le_rfl, h.transport.injection, h.transport.injection,
    h.transport.derivatives, h.phase.lengths⟩

theorem selected_pantry (h : Materializes X α s.kernel.spin) :
    Bid.Pantry S (α.ensemble α.atPoint) α.leaps X.derivatives α.slabs :=
  ⟨s.kernel, h.phase.states _, fun i => (h.phase.retains _ i).symm.le, h.transport.injection,
    h.phase.coordinates _, h.phase.calculus _, h.phase.goes⟩

theorem both (h : Materializes X α s.kernel.spin) (hk : K.Descends X.turns s.kernel.spin)
    {B D : Contour S} (hb : B.From S) (hd : D.From (α.ensemble α.atPoint)) :
    Compatible S α.unselected X K s.kernel.spin B ∧ Compatible S α.slabs X K s.kernel.spin D :=
  ⟨compatible (unselected_pantry (s:=s) h) h.transport.rights h.transport.motion h.transport.spots hk
      (fun _ => rfl) hb,
    compatible (selected_pantry (s:=s) h) h.transport.rights (h.phase.sym _) h.transport.spots hk
      (h.phase.retains _) hd⟩

/-- Produce, not assume, the chosen `Realizes`; unselected also with full
tubes, locality and field domain. -/
theorem after_materializes (h : Materializes X α s.kernel.spin) (K : Spins S)
    (hk : K.Descends X.turns s.kernel.spin) :
    ∃ (B D : Contour S) (F : Wightman S), F.spin=K ∧ Relativistic X α B D F s.kernel.spin ∧
      Compatible S α.unselected X K s.kernel.spin B ∧ Compatible S α.slabs X K s.kernel.spin D := by
  obtain ⟨B, hb⟩ := contour (unselected_pantry (s:=s) h)
  obtain ⟨D, hd⟩ := contour (selected_pantry (s:=s) h)
  obtain ⟨u, v⟩ := both (s:=s) h hk hb hd
  obtain ⟨F, hF, hK⟩ := v.vacuum h.phase.heat
  exact ⟨B, D, F, hK, ⟨hb, hd, hF⟩, u, v⟩


end both
end YM.Next.BOUNDARY
