import YM.Org.Input
import YM.Shift.Exchange
import YM.Shift.Osc


/-!
# Boundary/Fields Sinks. Sequenced without Wightman premise! Producer
proofs very much needed. Cups via exact Small. Pole geometry obligations
include common origin, parameter signs, Schwartz budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Org.Show
open Function Set Filter MeasureTheory Spec Table Extraction OS OS.Ground Boundary Probe
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S T : Table C.book}

structure Rhythm (S : Table C.book) {T : Table C.book} (V : Chamber T timeAxis) (A : Spread V) where
  bits : Small S V
  linked : bits.concretized A
  price p : Small.rated bits p
  lift : Waves S
  yields : bits.Defined lift
  birth : lift.Region T
  power : lift.Breathes ∧ lift.Bounds
  shore : lift.Lines ∧ lift.Along

namespace Rhythm
variable {V : Chamber T timeAxis} {A : Spread V}
lemma opens (Y : Rhythm (C:=C) S V A) : ∃ P : Surface S,Y.lift.NonTangentialFree P ∧ (Contour.mk Y.lift P).From T := by
  obtain ⟨W,hW⟩ := Y.lift.jointly Y.power.2 Y.shore.2 Y.shore.1 Y.power.1
  exact ⟨W,hW,Y.birth,Y.lift.exposed W hW⟩
end Rhythm

variable {V : Chamber T timeAxis} {A : Spread V}

/-- Include URS real Poincare + plane spectral small hypotheses because
such producers not licensed by the goal. Together with corner it's a
sufficient bridge for X; no stand-alone validity claim. -/
structure Lights (S : Table C.book) (K : Spins S) (Y : Rhythm (C:=C) S V A) (R : Surface S) : Prop where
  rotates : Urs R K
  axis : Y.lift.during R -- Transforms in absolute momentum vars
  braces : R.cone_tests

def Neon {K : Spins S} {Y : Rhythm (C:=C) S V A} {R : Surface S} (_ : Lights S K Y R) {D : ∀ n,Blanket n} (F : R.Aurora D) :=
    (∀ n : ℕ, (D n).Modified) ∧ F.FullBody Y.lift

structure Reveals (X : Algebra S) (K : Spins S) (J : StarOp S) (Y : Rhythm (C:=C) S V A) (R : Surface S) : Prop where
  I : Lights S K Y R
  visible : ∃ D,∃ F : R.Aurora D, Neon I F
  puncture : ∀ D (F : R.Aurora D), Neon I F → ∀ n (v : Fin n→S.Union) (P : NearPair n),
    ∃ y : ℕ → Heights n, Tendsto (dawn ∘ y) atTop (nhds 0) ∧
        ∀ m : ℕ, ∃ B : P.Panes F v (y m), B.sameGround ∧ B.Forms
  consistent : ∀ D (F : R.Aurora D), Neon I F → R.Persists
  water : Y.bits.Lamp R J K

/-- Four consumers only after exact outer contour. -/
structure Words (Y : Surface S) (K : Spins S) (J : StarOp S) : Prop where
  symbols : Y.Symbol
  motions : Urs Y K → Y.Strong J K ∧ Y.Transforms J K
  stiff : Y.Cam J
  locale : Actor Y → Y.Regional

variable {X : Algebra S} {K : Spins S} {J : StarOp S}
lemma uses {Y : Rhythm S V A} {R : Surface S} (H : Reveals X K J Y R) : Actor R ∧ R.Persists := by
  obtain ⟨D,F,hf⟩ := H.visible
  exact ⟨fun n v P => NearPair.actor F v P (hf.1 _) (tents _ _ H.I.rotates (H.I.braces n))
    (H.puncture _ F hf n v P),H.consistent D F hf⟩

lemma Reveals.harvest {h : S.RealSpin} {Y : Rhythm (C:=C) S V A} (HR : V.UniqueHeat) (hT : T.Basic) (hk : K.Descends X.turns h)
    (hp : S.Symmetric) (hx : X.derivatives.Inclusions S) (hv : starRead J h) {R : Surface S} (w : Reveals X K J Y R) (W : Words R K J)
    : ∃ B : Wightman S, B.Realizes (W:=R) X.turns h := by
  obtain ⟨he,hh⟩ := W.motions w.I.rotates
  obtain ⟨p,e⟩ := uses w
  exact Boundary.harvest J K hk hv (invol hp hx hv) W.symbols W.stiff e (W.locale p) he hh HR hT (Y.bits.bowls w.water)

variable {f : Extraction.Order} {s : Seed C f S} {α : Selection S}

structure Stage (s : Seed C f S) (X : Algebra S) (h : Materializes X α s.kernel.spin) (K : Spins S) (k : K.Descends X.turns s.kernel.spin) : Prop where
  songs : ∀ (T : Table C.book), T.Hierarchy → T.respects S → X.derivatives.Derivatives T → X.derivatives.Inclusions T →
    ∀ V : Chamber T timeAxis, ∀ A : Spread V, Spread.Laws A X.derivatives → Nonempty (Rhythm S V A (C:=C))
  beams (Y : Rhythm (C:=C) S α.leaps α.slabs) (W : Surface S) (J : StarOp S) (hj : starRead J s.kernel.spin) :
    Y.lift.NonTangentialFree W → Reveals X K J Y W
  solid (Y : Surface S) (J : StarOp S) (hj : starRead J s.kernel.spin) : Words Y K J

-- MayReveals uses THE chosen Ladder same as Γ ...
lemma Stage.go {h : Materializes (C:=C) X α s.kernel.spin} {Ht : K.Descends X.turns s.kernel.spin} (H : Stage s X h K Ht) :
    ∃ B D, ∃ Q : Wightman S, Relativistic X α B D Q s.kernel.spin := by
  let A := α.ensemble α.atPoint
  have he := h.phase.states α.atPoint
  have hv := h.transport.derivatives
  have hx := h.transport.injection
  obtain ⟨X0⟩ := H.songs S s.kernel (fun _ => le_rfl) hv hx α.room α.unselected h.phase.lengths
  obtain ⟨X1⟩ := H.songs A he (fun d => (h.phase.retains α.atPoint d).symm.le) (h.phase.calculus _) (h.phase.coordinates _) α.leaps α.slabs h.phase.goes
  let J := X.derivatives.unionAdj s.kernel.laws.toSymmetric hx timeAxis s.kernel.spin h.transport.rights
  have hr : starRead J s.kernel.spin := calibrate s.kernel.laws.toSymmetric hx _ _
  obtain ⟨u,Uh,U⟩ := X0.opens
  obtain ⟨v,Vh,V⟩ := X1.opens
  obtain ⟨Q,hQ⟩ := (H.beams X1 v J hr Vh).harvest h.phase.heat he.laws Ht s.kernel.laws.toSymmetric hx hr (H.solid v J hr)
  exact ⟨⟨_,_⟩,⟨_,_⟩,Q,U,V,hQ⟩
end YM.Org.Show
