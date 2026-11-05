import YM.Org.Twist


/-!
Proof requests. Names A.. DO NOT ADD ANSWERS HERE. Proof of each proposition, given no other hypotheses except what's explicitly taken
in that proposition. All polymorphic in one coherent cut. Names not A## e.g. Port also port definitions. Red at h₀ & input metrics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Set Function Filter Org Spec Extraction Climb Table Ward Spin
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius NNReal InnerProductSpace
variable {G : Gauge} {L : Register G} {S : Table L}

/-- Covariance and inclusions of angular map; mirror all H (for K internal H+ enough). -/
structure Hyper (H : S.RealSpin) (P : DiffPlan S) (D : Ward.SpinRows S) : Prop where
  real d u v : S.conj H d (D d u v) = D d u (S.conj H d v)
  inter d e (h : d ≤ e) u v : D e u (P.rise h v) = P.rise h (D d u v)
  unity d u : D d u (S.unit d)=0
  hex d (g : Signed) u v : S.mirror H d g (D d u v) = D d (orients g u) (S.mirror H d g v)

def A01 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (h : S.Hierarchy) (W : DiffPlan S),
    W.Derivatives S → W.Inclusions S → W.Orientation h.spin → ∀ J p Y, Climb.Pre h W J p Y →
    ColorLaw p W h.spin ∧ Hyper h.spin W Y

/-- Derivative as one shell shifts inside fixed χ. -/
structure ShellCom (V : DiffPlan S) (p : Climb.Parts S) (Y : Ward.SpinRows S) : Prop where
  moves : ∀ d b v u, V.deriv d b (Y d v u) + (∑ c : Axis, (↑(v.val c b):ℂ) • p d c u) = Y (d+1) v (V.deriv d b u)
  delta d b i u : V.deriv (d+1) b (p d i u) = p (d+1) i (V.deriv d b u)

def A02 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (h : S.Hierarchy) (W : DiffPlan S),
    W.Derivatives S → W.Inclusions S → ∀ J p Y, Climb.Pre h W J p Y → ShellCom W p Y


def LineSum (p : Climb.Parts S) := ∀ d n (b j : Axis), j ≠ b → ∀ v : Fin n → S.Field d, ∀ x : Points n, x∈conf _ → onLine b x →
    diagram v (leaves p d j) x=0

def A03 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (h : S.Hierarchy) (W : DiffPlan S),
    W.Inclusions S → W.Derivatives S → W.Orientation h.spin → ∀ p Y,
    ColorLaw p W h.spin → ShellCom W p Y → LineSum p → Climb.transverse p ∧ Climb.transverse W.deriv

/-- need flexible row testing: larger N,d,j,R always welcomed. -/
structure Watches (J : S.Stress) (T : Climb.Lighthouse L) (H : S.RealSpin) (a : (Bel L).RealSpin) (V : DiffPlan S)
    (P : Scaling S→ Prop) : Prop where
  ask : ∃ (D N m : ℕ) (R : ℝ), 1 ≤ R ∧ ∀ (X : Scaling S) (d : ℕ) (n k : ℕ) (B : ℝ),
    D ≤ d → N ≤ n → m ≤ k → R ≤ B → Track X V T J H a n d k B → P X

def ConLap (X : Scaling S) (P : Climb.Parts S) (d : ℕ) (G : Climb.Parts (Bel L)) (f : ℕ→ℝ) :=
    Tendsto (fun i => f i • X.aisle i d (leaves P d)) atTop (𝓝 (leaves G d))

def A04 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} (H : S.Hierarchy) (V : DiffPlan S),
    V.Inclusions S → V.Derivatives S → ∀ (R : MaxwellData C) (J : S.Stress) (d : ℕ),
    Watches J R.T H.spin R.hT.spin V (fun X => ConLap X V.deriv d R.T.W.deriv X.r)

def A05 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} (H : S.Hierarchy) (V : DiffPlan S),
    V.Inclusions S → V.Derivatives S → ∀ (R : MaxwellData C) (J : S.Stress) (d : ℕ)  (p : Climb.Parts S) (Y : Ward.SpinRows S),
    Pre H V J p Y →
    Watches J R.T H.spin R.hT.spin V (fun X => (ConLap X p d ((R.T.κ:ℝ) • R.T.W.deriv) (fun i => X.r i/X.xi i)) ∧
      ∀ j : Spin.Ind, Tendsto (fun i => (X.xi i)⁻¹ • (Spin.transport Y (X.U i d) j)) atTop (𝓝 (R.T.κ • Spin.leaf R.T.K.lie d j)))

def A06 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} (H : S.Hierarchy) (V : DiffPlan S),
    V.Inclusions S → V.Derivatives S → ∀ (R : MaxwellData C) (J : S.Stress) (d : ℕ) (p : Climb.Parts S),
    Climb.transverse p → Climb.transverse V.deriv → ColorLaw p V H.spin → ∀ e : Select C.book d,
    Ens e R.T.W R.hT.spin → Watches J R.T H.spin R.hT.spin V (fun X =>
      X.Align V R.T.W H.spin R.hT.spin (d+1) ∧ ∃ s : Subs e X,
      Tendsto s.moves atTop (𝓝 e.reads) ∧
      ∀ᶠ i in atTop, s.moves i (X.aisle i d (leaves V.deriv d))=0 ∧ s.moves i (X.aisle i d (leaves p d))=0)

/-- S instead of Bel after matrix assay. -/
def A07 : Prop := ∀ {G : Gauge} {C : Family G} {S : Table C.book} (H : S.Hierarchy) (V : DiffPlan S),
    V.Inclusions S → V.Derivatives S → V.Orientation H.spin → ∀ (R : MaxwellData C) (J : S.Stress), ActLaw V R.T J H.spin R.hT.spin →
    erases H.spin V

def Brackets {S : Table L} (Y : Ward.SpinRows S) := ∀ d u v, (Y d u).comp (Y d v)-(Y d v).comp (Y d u)=Y d (bracket u v)

def A08 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (H : S.Hierarchy) (V : DiffPlan S),
    V.Inclusions S → V.Derivatives S → V.Orientation H.spin → ∀ (Y : Ward.SpinRows S),
    (∀ n (x : Points n), x∈conf n → Still V Y x) → Hyper H.spin V Y → erases H.spin V → Brackets Y

/-- independent general Lie/polynomial lemma includes rel of P.lie at free in LH. -/
def A09 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (D : Ward.SpinRows S), Brackets D →
    rel D ∧ ∀ K : Ward.SpinRows S, Brackets K → ∀ d (z : List ℝ) i,
      Commute (wave z (leaf D d) (leaf K d)) (effect (leaf D d i) (leaf K d i))

/-- Brackets for free Port at every cap (support incoming optic startup + A09 use) -/
def A10 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (H : S.RealSpin) (R : Rotation S), Port R H →
    Brackets R.lie ∧ ∀ d (A : Ortho) g v, R.act d A (R.lie d g v)=R.lie d
      (⟨A.val*g.val*star A.val,by
        change star _ = -_; have H : star g.val= -g.val:=g.property; simp only [star_mul,star_star,H,neg_mul,← mul_assoc,mul_neg]⟩)
      (R.act d A v)

/-- Heat rank preserving commuting signed. -/
def A11 : Prop := A10 → ∀ {G : Gauge} {C : Family G} {S : Table C.book} (H : S.RealSpin) (K : DiffPlan S) (Y : Ward.SpinRows S),
    Hyper H K Y → ∀ (R : MaxwellData C) (d : ℕ) (U : Spin.change S d), realH H R.hT.spin U → ∀ z,
      Spin.wave z (transport Y U) (attach R.T.K d) ∈ Spin.preserves (Spin.fine R.hT.spin d)

/-- descent polynomial, not an assumption of normality in THIS inner product. -/
def A12 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (T : Rotation S) (H : S.RealSpin),
    Port T H → ∀ d, ∃ p : List ℝ, Works p (leaf T.lie d)

/-- universal group generation by H & one-parameter. -/
def AxisGens := Subgroup.closure ((Set.range Signed.ortho) ∪ {x : Ortho|∃ (g : Ortho.Skew) (t : ℝ),Ortho.oneParameter g t=x})
def A13 : Prop := AxisGens=⊤

def A14 : Prop := A13 → ∀ {G : Gauge} {L : Register G} {S : Table L} (H : S.Hierarchy) (V : DiffPlan S),
    V.Inclusions S → V.Derivatives S → ∀ U : Rotation S, Port U H.spin →
    (∀ n (x : Points n), x∈conf n → Still V U.lie x) → U.Laws V H.spin ∧ U.Oriented S

def A15 : Prop := A10 → ∀ {G : Gauge} {L : Register G} {S : Table L} (H : S.Hierarchy) (V : DiffPlan S),
    V.Inclusions S → V.Derivatives S → V.Orientation H.spin → ∀ (X : Rotation S), X.Laws V H.spin → X.Oriented S →
    ∀ J p Y c, Crystal H V J p Y c → X.lie=c⁻¹ • Y → ∃ J' : Stress S, Conserved V H.spin J' ∧
      Tensorial X J' ∧ StressLaws S J' V.deriv X.lie
open Mink Boundary
def beamGens := Subgroup.closure ({x : Lorentz | ∃ (K : Ortho) (h : Lorentz.spatialTurn K), Lorentz.room K h = x} ∪
    {x : Lorentz | ∃ (i : SpaceAxis) (t : ℝ),(Ray.fromAxis i).boost t=x})
def A16 : Prop := beamGens=⊤

def A17 : Prop := A16 → ∀ {G : Gauge} {C : Family G} {S : Table C.book} {F} (V : DiffPlan S) (W : MaxwellData C) (I)
    (H : UV C F S V W I) (c : ℝ) (U : ∀ d,Spin.change S d) (J), Tab S V W I H c U J → wand V U W.vacuum

end YM.Bid
