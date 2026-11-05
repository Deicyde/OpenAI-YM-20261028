import YM.Bid.Corners
import YM.Shift.Exchange
/-!
# Lamp and charter W-domain bids
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Function Set Filter Analysis Spectral MeasureTheory Measure Distribution Mink Mink.Poincare Boundary Boundary.Surface Probe OS OS.Semigroup Complex Spec Org
open scoped Topology InnerProductSpace BigOperators NNReal ENNReal ContDiff FourierTransform
variable {G : Gauge} {L : Register G} {n m : ℕ} {S T : Table L} {V : Chamber T timeAxis}

def bothH (x : Heights n) (y : Heights m) : Heights (n+m) := Fin.append (fun i => -x i.rev) y
def bothP (x : Points n) (y : Points m) : Points (n+m) := points (Fin.append (fun i : Fin n => x i.rev) y.ofLp)

def bothT (v : Fin n → S.Union) (w : Fin m → S.Union) (J : StarOp S) : Fin (n+m) → S.Union := Fin.append
    (fun i : Fin n => J (v i.rev)) w

structure Hull (B : Small S V) (F : Waves S) (J : StarOp S) : Prop where
  join : ∀ n m (v : Fin n → S.Union) (w : Fin m → S.Union) (t u : ℝ≥0) (x : Heights n) (y : Heights m),
    x∈positiveHeight n → y∈positiveHeight m → Small.ample t x → Small.ample u y → ∀ (r : Points n) (p : Points m),
    inner ℂ (B.shot t n v x r) (B.shot u m w y p) = F.restricted (bothT v w J) (bothH x y) (bothP r p)

structure Roof (B : Small S V) (K : Spins S) : Prop where
  uses (b : Sentence S) (t : ℝ) (h : 0<t) : Integrable (fun x =>
    (Joint.materialize b.length (fun i => (b.get i).2) x) • B.shot (Small.logD t) _ (fun i => (b.get i).1) (Small.profile t b.length) x)
  time (v b) (k : ℝ) (h : 0<k) : B.heatCup (K.po (translation b) v) k = V.flow.unit.translation b (B.heatCup v k)

def C22 : Prop := ∀ {G : Gauge} {L : Register G} (S T : Table L) (V : Chamber T timeAxis) (P : DiffPlan S)
    (A : Spread V) (B : Small S V) (F : Waves S) (H : Pantry S T V P A) (J : StarOp S), starRead J H.head.spin →
    Direct A B F → (P.Orientation H.head.spin) → T.respects S → Hull B F J

def C23 : Prop := ∀ {G : Gauge} {L : Register G} (S T : Table L) (V : Chamber T timeAxis) (P : DiffPlan S)
    (A : Spread V) (B : Small S V) (K : Spins S) (R : S.Rotation) (H : Pantry S T V P A), Piece A B → K.Descends R H.head.spin → Roof B K

def C24 : Prop := ∀ {G : Gauge} {L : Register G} (S T : Table L) (V : Chamber T timeAxis) (P : DiffPlan S)
    (A : Spread V) (B : Small S V) (F : Waves S) (J : StarOp S) (K : Spins S) (W : Surface S),
    Pantry S T V P A → F.Region T → F.NonTangentialFree W → Roof B K → Hull B F J → B.Lamp W J K

-- density CAREFUL n=0 materialize constant

def C25 : Prop := ∀ (n : ℕ), Submodule.topologicalClosure (Submodule.span ℂ (Set.range (Joint.materialize n)))=⊤

def C26 : Prop := C25 → ∀ {G : Gauge} {L : Register G} (S T : Table L) (W : DiffPlan S) (D : ∀ n, Blanket n)
    (U : Surface S) (B : Waves S) (F : U.Aurora D), (∀ d, T.null d=S.null d) → T.Hierarchy → S.Hierarchy → W.Inclusions S →
    W.Inclusions T → B.Region T → F.FullBody B → U.Persists

def C27 : Prop := ∀ {G : Gauge} {L : Register G} (S : Table L) (W : Surface S), Actor W → W.Regional

def C28 : Prop := C08 → ∀ {G : Gauge} {L : Register G} (S : Table L) (W : Surface S) (J : StarOp S) (K : Spins S)
    (R : S.Rotation) (P : DiffPlan S) (h : S.RealSpin), S.Symmetric → P.Inclusions S → K.Descends R h → starRead J h →
    Urs W K → W.Strong J K ∧ W.Transforms J K

def C29 : Prop := ∀ {G : Gauge} {L : Register G} (S : Table L) (W : Surface S) (J : StarOp S), W.Symbol ∧ W.Cam J
end YM.Bid
