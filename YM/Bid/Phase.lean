import YM.OS.Train
import YM.Org.Phase

/-!
# Proof bids -- counts via registry only

B..., prepared to be proved in isolation. `Bench` is a red coarsening-gate (S API
through births), chosen link sizes & exteriors grouped under smaller grid;
keep all-cell uniformity; not inferred from lattice code yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Set Filter Function MeasureTheory OS OS.Ground Org Org.Phase Spec Table Word Analysis Extraction
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff ENNReal

variable {G : Gauge} {L : Register G} {S T : Table L}

def FitsSeat (C : Family G) (k : ℕ) (y : ℝ≥0) := ∃ n : ℕ, y.val= (n:ℝ)*C.S.a k

def Bench {G : Gauge} (C : Family G) (S : Table C.book) := ∀ D (R : ℝ), ∃ C₀ : ℝ, ∃ P : ℕ, 0<C₀ ∧
    ∀ d : ℝ≥0, ∀ w : C.book.Word, w≠[] → constrained D R w → Slab timeAxis d w → ∀ r : ℝ, 0<r → r ≤ 1 → buffer timeAxis r d w →
    ∃ (b : ℕ) (s : ℝ≥0), s≤d ∧ FitsSeat C b s ∧ ∃ h : Slab timeAxis s w,
    QRead S (Spread.radius C₀ P w r) h


def Seats : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} {F : Order}, Seed C F S → Bench C S

def B01 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} (V : Chamber S timeAxis),
    S.Hierarchy → Bench C S → ∃ A : Spread V,A.AllCopy

/-- Smooth Up & derivative. Used twice; any Bread respects S.
Position torsion can be controlled by observing against DENSE vectors then using uniformly bounded operator derivatives.
-/
def B02 : Prop := ∀ {G : Gauge} {L : Register G} (S T : Table L) (P : DiffPlan S) (V : Chamber T timeAxis)
    (A : Spread V), S.Hierarchy → T.Hierarchy → T.respects S → S.Symmetric → T.Symmetric →
    P.Derivatives T → A.AllCopy → A.Laws P

section
variable (V : Chamber S timeAxis) (A : Spread V) {n : ℕ}
open scoped Classical in
def depot (x : Points n) (p : Caps n) (v : L.Vector p) : A.algebra :=
    if h : x∈conf n then M A (realize (fun i => ⟨p i,v i⟩) x) (realized .. |>.2 h) else 0

structure Theme : Prop where
  vacant : M A [] (locations.mpr (by simp))=1
  array (n : ℕ) (p : Caps n) (x : Points n) : ∃ U : MultilinearMap ℂ (fun i => L.Ref (p i)) (↥A.algebra),
    ∀ t : L.Vector p, U t=depot V A x p t
  unital {n : ℕ} (d : ℕ) (x : Points (n+1)) (v : Fin n → L.Token) (hx : x∈conf _) :
    M A (realize (Fin.cons (α:=fun _ => L.Token) (L.one d) v) x) ((realized _ _).2 hx) = M A (realize v (Points.tail x)) ((realized _ _).2 (Points.tail_in hx))
  changes {v w} (h : List.Perm v w) (hp : distinct v) (hw : distinct w) : M A v hp=M A w hw
  offsets x (v : L.Word) (h : distinct v) : M A v h=M A (carry v x) (still h x)
  steep n (v : Fin n → L.Token) : ContDiffOn ℝ ∞ (fun x : Points n => (depot V A x (fun i => (v i).1) (fun i => (v i).2)).val) (conf n)
  opposite (w : L.Word) (h : distinct w) : ∀ h', star (M A w h)= M A (reflect w timeAxis) h'
  pins (n : ℕ) (p : Caps n) (x : Points n) (v w : L.Vector p) (h : ∀ i,S.project (p i) (v i)=S.project (p i) (w i)) :
    depot V A x p v=depot V A x p w
end

def B03 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (_ : S.Hierarchy) (D : DiffPlan S)
    (V : Chamber S timeAxis) (A : Spread V), Steady V → A.Laws D → Theme V A

def B04 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} {F : Order} {n : ℕ} (v : Fin n→C.book.Token) (w : Fin n→ Lattice.Cover)
    (k : ℕ), C.Makes → S.Hierarchy → F.PointLimits C S → Grid.plain (C:=C) v → Order.grid C k w∈generic n → Grid.Expects (S:=S) (f:=F) k v w

def B05 : Prop := B04 → ∀ {G : Gauge} {C : Family G} {S : Table C.book} {F : Order} (s : Seed C F S) (_ : Grill C F)
    (X : Algebra S), Locals X s.kernel.spin → ∀ V : Chamber S timeAxis, ∀ A : Spread V, Steady V → Theme V A → Phase.reflects (C:=C) V A

def B06 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} (V : Chamber S timeAxis) (A : Spread V) (T : Rotation S)
    (P : DiffPlan S) (H : S.Hierarchy), T.Oriented S → T.Laws P H.spin → Theme V A → Steady V → Phase.reflects (C:=C) V A →
    ∀ K : Ortho, ∀ w,∀ h : distinct w, ∀ p, M A w h=M A (Ground.rotate w T K) p

structure Garland {G : Gauge} {C : Family G} {S : Table C.book} (V : Chamber S timeAxis) (A : Spread V) (P : Spread.Resolution A)
    (p : P.X → Table C.book) (X : Algebra S) : Prop where
  threads (i : P.X) : P.receives (p i) i
  basics i : (p i).Basic
  HOnly i : (p i).RealSpin
  translation i : (p i).Homogeneous
  rel i : (p i).respects S
  turns i : X.turns.Oriented (p i)
  smooth i : (p i).Smooth

def B07 : Prop := B06 → ∀ {G : Gauge} {C : Family G} {S : Table C.book} (V : Chamber S timeAxis) (A : Spread V)
    (P : Spread.Resolution A) (X : Algebra S) (H : S.Hierarchy), Locals X H.spin → Theme V A → Steady V → Phase.reflects (C:=C) V A →
    P.Out → ∃ p, Garland V A P p X

/-- reflection positivity for every state including smearing (Lebesgue)
 and all axes. -/
def B08 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} (V : Chamber S timeAxis) (A : Spread V)
    (P : Spread.Resolution A) (X : Algebra S) (H : S.Hierarchy), Locals X H.spin → Steady V →
    P.Out → ∀ p, Garland V A P p X → ∀ i, (p i).RP ∧ (p i).RPSmear

def B09 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} (V : Chamber S timeAxis) (A : Spread V)
    (P : Spread.Resolution A) (R : Algebra S) (H : S.Hierarchy), Locals R H.spin → Steady V → Theme V A → A.Laws R.derivatives →
    P.Out → ∀ p, Garland V A P p R → ∀ i, R.derivatives.Inclusions (p i) ∧ R.derivatives.Derivatives (p i) ∧
      Table.StressLaws (p i) R.energy R.derivatives.deriv R.turns.lie

def OneCap (S : Table L) := ∀ n (d : Caps n) (v : L.Vector d), ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧
  ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x : Points n, spaced r x → ‖S.value d x v‖ ≤ C * r⁻¹ ^ A

/-- (S:=T at Org.Input Arrival); elsewhere works before T.respects reverse. -/
def B10 : Prop := ∀ {G : Gauge} {L : Register G} (S T : Table L) (W : DiffPlan S), T.respects S →
    T.Smooth → T.Basic → W.Inclusions T → W.Derivatives T → OneCap T → T.Capped

def B11 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} (V : Chamber S timeAxis) (A : Spread V)
    (P : Spread.Resolution A) (X : Algebra S), Steady V → A.AllCopy → P.Out → ∀ p,
    Garland V A P p X → ∀ i, OneCap (p i)

def B12 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (V : Chamber S timeAxis) (A : Spread V),
    S.Hierarchy → Theme V A → Steady V → ∃ T : ℕ→A.algebra, DenseRange T

def B13 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} (V : Chamber S timeAxis) (A : Spread V)
    (P : Spread.Resolution A) (X : Algebra S) (H : S.Hierarchy), Locals X H.spin → Steady V → A.Laws X.derivatives → Theme V A → P.Out →
    ∀ p, Phase.Scripts X V A P p → ∀ i (Z : Chamber (p i) timeAxis), ∃ B : Spread Z,B.AllCopy

def B14 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} (V : Chamber S timeAxis) (A : Spread V)
    (P : Spread.Resolution A) (X : Algebra S) (p : P.X→Table C.book), S.Hierarchy → Steady V → Theme V A → P.Out → Phase.Scripts X V A P p →
    ∀ W : ∀ i, Chamber (p i) timeAxis, ∃ R : ℕ→Future C.book timeAxis, ∀ i, Cluster.horizon (W i) R
end YM.Bid
