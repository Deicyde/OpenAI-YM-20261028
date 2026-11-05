import YM.Next.RANK.Guard
import YM.Next.RANK.Joints


/-!
# Leading joint emulator for a one-step contribution

Orders before interacting R errors and before ANY W calculations. Always the
actual Rank trajectory, masks with full footprints. H-leading terms in THIS
one propagation from frame gate must match C. At one allowed output T, one law
(potentially mixture over finitely many tags, not necessarily same law at other
T). Uses only input frames potentially present. The field read in this law is
not required to be a conditional probability for the full step; it's an
auxiliary distribution for the stated leading contributions. Needed input on
any gQ configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Set MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge}
variable (C : Family G) {i k l j m p q d D a n N : ℕ}
variable (R : Lead G C.S p)

abbrev Marquee (k : ℕ) (b : ℝ) (p d : ℕ) (x : Points n) (h : i≤k) := Index x b C.path.levels p d h

def anneals (F : Course C N p k) (j) := (Real.sqrt (F.changeβ j))⁻¹
lemma warmth (F : Course C N p k) {j} (h : j ≤ N): 0<anneals C F j:=by have := F.pos j h; unfold anneals; positivity
lemma bootwarm (F : Course C N p k) (h : k ≤ N) : anneals C F k=LiftMark.GaugeScale C k N p:= by rw [anneals,F.same k le_rfl h];rfl

variable {C}
variable {hN : k≤N} {b : ℝ} {x : Points n} {hk : i<k} {h : middle C.path.levels b k ≤ i}
variable {c : Course C N p k}
variable (F : CellP C k b p)

def basisK (F : Course C N p k) (x : Points n) (b : ℝ) (j) (hN : k≤N) (p' : j≤k) (hp : middle C.path.levels b k ≤ j) (i : CellP C k b p) (v : pennant n) (U : Config G (C.side j p)) :=
    let D:= watches C b p hN j hp i U
    let o:= core C.path.levels x b p p' (headMark v)
    kiosk (anneals C F j) o D

def colorMean (c : Course C N p k) (b : ℝ) (x : Points n) (hk : i<k) (h : middle C.path.levels b k ≤ i) (j : CellP C k b p) (v : pennant n) (U : Config G (C.side i p)) :=
    let m:= basisK c x b i c.allow hk.le h j v U
    Normal.reads (R i).H (fun i=>(↑(rigid m i):ℂ))

def tests (x : Points n) (s : ℝ) (hk : i<k) (Q : pennant n) (u : Index x s C.path.levels p d (show i+1≤k from hk)) := (tale u.val).val.val ⊆ (tale Q).val.val

def spokes (x : Points n) (s : ℝ) (hk : i<k) (d : ℕ) (Q : pennant n) : Finset (Chamber G C.S (i+1) p):=
    Finset.univ.filter fun i' => ∃ u : Index x s C.path.levels p d (show i+1≤k from hk),tests (C:=C) x s hk Q u∧ spotP s (i+1) d (show i+1≤k from hk) (C:=C) x u.val i'

structure Emulator (c : Course C N p k) (R : Lead G C.S p) (x : Points n) (b : ℝ) (hk : i<k) (h : middle C.path.levels b k ≤ i) (q : ℕ) (T : Lane C k b p d x hk.le) (τ : ℝ)
    (U : Config G (C.side i p)) (ε : ℝ) where
  Θ : Type
  M : MeasurableSpace Θ
  μ : Measure Θ
  -- normalized real array of centered fine curvature variables on this tag; zero columns can remain active
  η : Θ → Chamber G C.S (i+1) p→ℝ
  P : Normal.Symmetric (Chamber G C.S (i+1) p)
  initial : VMeasure Θ _ μ η P
  -- true fine inputs to this W.E principal vertex
  V : Θ→ Config G (C.side (i+1) p)
  census : Measurable V
  reach i' (hx : i'∈spokes (C:=C) x b hk d T.2.val) j (hj : j∈spokes (C:=C) x b hk d T.2.val): ‖P.cov i' j -(R i).Q.cov i' j‖≤ ε
  Γ : Marquee C k b p d x (show i+1≤k from hk)→ Θ →ℝ
  lives a : tests (C:=C) x b hk T.2.val a → Guarded (Γ a) (ε^2) μ
  field a : tests (C:=C) x b hk T.2.val a → ∀ θ, 0 < Γ a θ → Healthy τ (dolmens (C:=C) (p:=p) x b q
    (walls (clim C.path.levels (i+1))) c.allow (show i+1≤k from hk) T.1 a.val) (V θ)
  -- permit change of frame for each S (even tag/exterior field dependent),
  -- not choosing per leg. Lookups all on joint μ.
  wraps a : tests (C:=C) x b hk T.2.val a → ∀ θ, 0 < Γ a θ →
    ∃ Z : G.El,∀ j : Chamber G C.S (i+1) p, spotP b (i+1) d (show i+1≤k from hk) (C:=C) x a.val j →
      |rigid (coloring Z (basisK c x b (i+1) c.allow (show i+1≤k from hk)
           (h.trans (Nat.le_succ i)) T.1 a.val (V θ))) j -((colorMean R c b x hk h T.1 T.2.val U j).re + η θ j)| ≤ ε

-- Choice of mixture needs no monomials. quadrature joint for all relevant subsets
structure StageX (c : Course C N p k) (R : Lead G C.S p) (x : Points n) (b : ℝ) (hk : i<k) (h : middle C.path.levels b k ≤ i) (q : ℕ) (T : Lane C k b p d x hk.le) (τ : ℝ) (U : Config G (C.side i p)) (ε : ℝ) where
  count : ℕ
  tag : Fin count → Emulator c R x b hk h q T τ U ε
  weight : Fin count→ ℝ
  pos i : 0 ≤ weight i
  total : ∑ j,weight j=1

section
variable {R} {U T τ ε} (E : StageX (d:=d) c R x b hk h q T τ U ε)

-- output coefficients in estimate even before orientation. Raw tests for ALL W inputs not specified pols.


variable (W : Index x b C.path.levels p d (show i+1≤k from hk)→ Config G (C.side (i+1) p)→ℂ)

def planted j a ω := (↑((E.tag j).Γ a ω):ℂ)* W a ((E.tag j).V ω)
def planter (j : Fin E.count) (ω : (E.tag j).Θ) : veil (Fin n) :=
    ∑ a : Index x b C.path.levels p d (show i+1≤k from hk), if tests x b hk (C:=C) T.2.val a then
      Poly.send (tale a.val).val (planted E W j a ω) else 0

def mixedEval (s : Fin E.count → ℂ) := ∑ j : Fin E.count,(E.weight j:ℂ)*s j

def plaids (x : (j : Fin E.count) → (E.tag j).Θ →ℂ) := mixedEval E fun j =>
    letI := (E.tag j).M
    ∫ z, x j z ∂ (E.tag j).μ

def planters : veil (Fin n) := Poly.inject fun i=> plaids E fun j z => (Poly.pass (planter E W j z)).part i
lemma unquiet (j) (ω): (planter E W j ω).part (quiet _)=0 := by
  rw [planter, Poly.part_sum]; apply Finset.sum_eq_zero; intro v _; split
  · exact send_zero _ _ (tale v.val).property
  rfl
lemma plaid_const (i : ℂ) : plaids E (fun _ _=>i)=i:= by
  have he j : letI:= (E.tag j).M; (∫ _, i ∂ (E.tag j).μ)=i:= by letI:=(E.tag j).M; haveI: IsProbabilityMeasure (E.tag j).μ:= (E.tag j).initial.norm; simp
  unfold plaids mixedEval; rw [show ∑ j,_ = ∑ j,(E.weight j:ℂ)*i from Finset.sum_congr rfl (fun j _=> congr_arg _ (he j)),← Finset.sum_mul,← Complex.ofReal_sum,E.total]; simp
lemma planters_one : (planters E W).part (quiet _)=1:= by
  change plaids E (fun j z=> _)=1
  simp_rw [Poly.pass_part _ (unquiet E W ..),plaid_const]

-- compare to Wcur only after forecasts paid

def leadQ := connected (planters E W) (planters_one E W)
end
end YM.Next.Rank.Tapes
