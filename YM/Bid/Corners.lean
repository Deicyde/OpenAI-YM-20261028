import Mathlib.Analysis.Fourier.AddCircleMulti
import YM.Bid.Angular




/-!
# Show.Stage trajectory, strict contour tasks

No use of W.Reconstruction as premise. Tickets prove props WITHOUT imports of
other tickets; can *assume* e.g. C09 if expressly an argument of target.
Priority cost frontier with axes hot. Fourier sign RADIAN.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Set Filter Function MeasureTheory OS OS.Ground Org  Spec Table Analysis Extraction Boundary Boundary.Small LineDeriv Complex Mink
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff ENNReal

variable {G : Gauge} {L : Register G} {n : ℕ} {S T : Table L}
variable {V : Chamber T timeAxis}

structure Pantry (S T : Table L) (V : Chamber T timeAxis) (P : DiffPlan S) (A : Spread V) : Prop where
  head : S.Hierarchy
  adopted : T.Hierarchy
  present : T.respects S
  rises : P.Inclusions S
  habits : P.Inclusions T
  Der : P.Derivatives T
  counter : A.Laws P

-- issue actual from alpha and from any T pane constructed separately
structure Piece (A : Spread V) (B : Small S V) : Prop where
  bits : B.concretized A
  price : ∀ v, Small.rated B v

def C01 : Prop := ∀ {G : Gauge} {L : Register G} (S T : Table L) (V : Chamber T timeAxis) (P : DiffPlan S) (A : Spread V),
    Pantry S T V P A → ∃ B : Small S V, Piece A B

structure Slice (A : Spread V) (B : Small S V) : Prop where
  stature : Piece A B
  pure {n : ℕ} (p : ℝ≥0) (y : Heights n) (x : SpacePoints n) (v : Fin n → S.Tag) (h : y∈east n) (hp : enough y p) :
    Small.matrix B p n (fun i => ↑(y i)*Complex.I) x (fun i => S.pin (v i).1 (v i).2) = S.useAt T (place x y) v
  same {n : ℕ} {z : Times n} (x : SpacePoints n) (p : Fin n → S.Union) (q l : ℝ≥0) (hp : z∈strict n) (h : lit z q) (hk : lit z l) :
    B.matrix q n z x p=B.matrix l n z x p

def C02 : Prop := ∀ {G : Gauge} {L : Register G} (S T : Table L) (V : Chamber T timeAxis) (P : DiffPlan S) (A : Spread V)
    (B : Small S V), Pantry S T V P A → Piece A B → Slice A B

structure Direct (A : Spread V) (B : Small S V) (F : Waves S) : Prop where
  linked : Slice A B
  tune : B.Defined F
  reach : F.Region T
  birth : F.Breathes

def C03 : Prop := ∀ {G : Gauge} {L : Register G} (S T : Table L) (V : Chamber T timeAxis) (A : Spread V)
    (B : Small S V), Slice A B → ∃ F : Waves S, Direct A B F

def C04 : Prop := ∀ {G : Gauge} {L : Register G} (S T : Table L) (F : Waves S),
    F.Region T → F.Breathes → F.Bounds ∧ F.Along ∧ F.Lines

def C05 : Prop := ∀ {G : Gauge} {L : Register G} (S T : Table L) (F : Waves S) (W : Surface S),
    F.Region T → F.Breathes → F.Lines → F.Along → F.NonTangentialFree W → F.during W

def C06 : Prop := ∀ {G : Gauge} {L : Register G} (S T : Table L) (F : Waves S) (W : Surface S),
    F.Region T → F.Breathes → F.Bounds → F.during W → W.cone_tests

-- Strong test push, differential around identity only (enough for autonomous boosts).
def realTerm (i : Fin n) (a : Axis) (f : Joint n) := ∂_{Points.direction i a} f

def coo (i : Fin n) (a : Axis) (x : Points n) : ℝ := x i a

-- choose Real scalars on Schwartz? `smulLeftCLM` use ℂ! value proof below.
def multiplier (i : Fin n) (a : Axis) := (SchwartzMap.smulLeftCLM ℂ (fun x => (coo i a x:ℂ)) : Joint n→L[ℂ] Joint n)

/-- verify shape of a source differential call -/
lemma multiplier_test (i : Fin n) (a : Axis) (f : Joint n) (x : Points n) : multiplier i a f x = (↑(x i a):ℂ) * f x := by
  unfold multiplier
  let e := Points.flatten (n := n)
  have hp := (show HasTemperateGrowth (fun x : Points n => ((↑(e x (i,a)):ℂ))) from
    ((((Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ => ℝ) (i,a))).comp e.toContinuousLinearEquiv.toContinuousLinearMap)).hasTemperateGrowth))
  exact SchwartzMap.smulLeftCLM_apply_apply hp f x

def inclined (a : SpaceAxis) (y : Heights n) (f : Joint n) :=
    ∑ i, (multiplier i a.castSucc (realTerm i timeAxis f)+ multiplier i timeAxis (realTerm i a.castSucc f) + ((y i:ℂ)*I) • realTerm i a.castSucc f)

def kick (X : Rotation S) (k : SpaceAxis) (v : S.Tag) : S.Union := S.pin v.1
    ((-I:ℂ) • X.lie v.1 (Ortho.plane timeAxis k.castSucc) v.2)

def ink (v : Fin n → S.Tag) (i : Fin n) := S.pin (v i).1 (v i).2

def Boosty (X : Rotation S) (F : Waves S) := ∀ n (v : Fin n → S.Tag) (a : SpaceAxis) (f : Joint n) (y : Heights n), y ∈ east n →
    (∑ i, F.psi (Function.update (ink v) i (kick X a (v i))) y f) = F.psi (ink v) y (inclined a y f)

def C07 : Prop := ∀ {G : Gauge} {L : Register G} (S T : Table L) (R : Rotation S) (K : Spins S) (h : S.Hierarchy)
    (V : DiffPlan S), V.Inclusions S → T.Hierarchy → T.respects S → R.Oriented T → R.Laws V h.spin → K.Descends R h.spin →
    ∀ Y : Waves S, Y.Region T → Y.Breathes → Y.Bounds → Y.Lines → Y.Along → Boosty R Y

def C08 : Prop := (∀ n (f : Joint n), Continuous (fun p : Poincare => Joint.gpush n p f)) ∧ ∀ n (f : Joint n) a,
    Tendsto (fun i : ℝ => i⁻¹ • (Joint.gpush n (Poincare.motion ((Ray.fromAxis a).boost i)) f - f))
      (𝓝[≠] 0) (𝓝 (-inclined a 0 f)) -- strong Schwartz topology

def C09 : Prop := A16 → C08 → ∀ {G : Gauge} {L : Register G} (S T : Table L) (R : Rotation S) (K : Spins S)
    (h : S.Hierarchy) (V : DiffPlan S), V.Inclusions S → T.Hierarchy → T.respects S → R.Oriented T →
    R.Laws V h.spin → K.Descends R h.spin → ∀ (Y : Waves S) (W : Surface S),
    Y.Region T → Y.Breathes → Boosty R Y → Y.NonTangentialFree W → Urs W K
end YM.Bid
