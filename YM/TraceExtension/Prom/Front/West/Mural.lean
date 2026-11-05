import YM.MergeProof.West.Mural
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.MergeProof.West.Mural for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Set MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge}
variable (C : Family G) {i k l j m p q d D a n N : ℕ}
variable (R : Lead G C.S p)

variable {C}
variable {hN : k≤N} {b : ℝ} {x : Points n} {hk : i<k} {h : middleSky C.path.levels b k ≤ i}
variable {c : Course C N p k}
variable (F : CellPSky C k b p)

def basisFtSky (F : Course C N p k) (x : Points n) (b : ℝ) (j) (hN : k≤N) (p' : j≤k) (hp : middleSky C.path.levels b k ≤ j) (i : CellPSky C k b p) (v : Manner n) (U : Config G (C.side j p)) :=
    let D:= watchesSky C b p hN j hp i U
    let o:= core C.path.levels x b p p' (Head v)
    kiosk (anneals C F j) o D

def colorFtSky (c : Course C N p k) (b : ℝ) (x : Points n) (hk : i<k) (h : middleSky C.path.levels b k ≤ i) (j : CellPSky C k b p) (v : Manner n) (U : Config G (C.side i p)) :=
    let m:= basisFtSky c x b i c.allow hk.le h j v U
    Normal.reads (R i).H (fun i=>(↑(rigid m i):ℂ))

structure MuralSky (c : Course C N p k) (R : Lead G C.S p) (x : Points n) (b : ℝ) (hk : i<k) (h : middleSky C.path.levels b k ≤ i) (q : ℕ) (T : BaleSky C k b p d x hk.le) (τ : ℝ)
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
  reach i' (hx : i'∈sp_okes (C:=C) x b hk d T.2.val) j (hj : j∈sp_okes (C:=C) x b hk d T.2.val): ‖P.cov i' j -(R i).Q.cov i' j‖≤ ε
  Γ : ViewFt C k b p d x (show i+1≤k from hk)→ Θ →ℝ
  lives a : t_ests (C:=C) x b hk T.2.val a → Guarded (Γ a) (ε^2) μ
  field a : t_ests (C:=C) x b hk T.2.val a → ∀ θ, 0 < Γ a θ → Healthy τ (d_olmSky (C:=C) (p:=p) x b q
    (walls (clim C.path.levels (i+1))) c.allow (show i+1≤k from hk) T.1 a.val) (V θ)
  -- permit change of frame for each S (even tag/exterior field dependent),
  -- not choosing per leg. Lookups all on joint μ.
  wraps a : t_ests (C:=C) x b hk T.2.val a → ∀ θ, 0 < Γ a θ →
    ∃ Z : G.El,∀ j : Chamber G C.S (i+1) p, spotFt b (i+1) d (show i+1≤k from hk) (C:=C) x a.val j →
      |rigid (coloring Z (basisFtSky c x b (i+1) c.allow (show i+1≤k from hk)
           (h.trans (Nat.le_succ i)) T.1 a.val (V θ))) j -((colorFtSky R c b x hk h T.1 T.2.val U j).re + η θ j)| ≤ ε

-- Choice of mixture needs no monomials. quadrature joint for all relevant subsets
structure StageNowSky (c : Course C N p k) (R : Lead G C.S p) (x : Points n) (b : ℝ) (hk : i<k) (h : middleSky C.path.levels b k ≤ i) (q : ℕ) (T : BaleSky C k b p d x hk.le) (τ : ℝ) (U : Config G (C.side i p)) (ε : ℝ) where
  count : ℕ
  tag : Fin count → MuralSky c R x b hk h q T τ U ε
  weight : Fin count→ ℝ
  pos i : 0 ≤ weight i
  total : ∑ j,weight j=1

section
variable {R} {U T τ ε} (E : StageNowSky (d:=d) c R x b hk h q T τ U ε)

-- output coefficients in estimate even before orientation. Raw t_ests for ALL W inputs not specified pols.

variable (W : PatchPt x b C.path.levels p d (show i+1≤k from hk)→ Config G (C.side (i+1) p)→ℂ)

def p_lantedSky j a ω := (↑((E.tag j).Γ a ω):ℂ)* W a ((E.tag j).V ω)
def p_lanterSky (j : Fin E.count) (ω : (E.tag j).Θ) : veil (Fin n) :=
    ∑ a : PatchPt x b C.path.levels p d (show i+1≤k from hk), if t_ests x b hk (C:=C) T.2.val a then
      Poly.send (tag a.val).val (p_lantedSky E W j a ω) else 0

def mixedFtSky (s : Fin E.count → ℂ) := ∑ j : Fin E.count,(E.weight j:ℂ)*s j

def plaidFtSky (x : (j : Fin E.count) → (E.tag j).Θ →ℂ) := mixedFtSky E fun j =>
    letI := (E.tag j).M
    ∫ z, x j z ∂ (E.tag j).μ

def planterFtSky : veil (Fin n) := Poly.inject fun i=> plaidFtSky E fun j z => (Poly.pass (p_lanterSky E W j z)).part i
lemma un_quietSky (j) (ω): (p_lanterSky E W j ω).part (quiet _)=0 := by
  rw [p_lanterSky, Poly.part_sum]; apply Finset.sum_eq_zero; intro v _; split
  · exact send_zero _ _ (tag v.val).property
  rfl
lemma plaidF_constSky (i : ℂ) : plaidFtSky E (fun _ _=>i)=i:= by
  have he j : letI:= (E.tag j).M; (∫ _, i ∂ (E.tag j).μ)=i:= by letI:=(E.tag j).M; haveI: IsProbabilityMeasure (E.tag j).μ:= (E.tag j).initial.norm; simp
  unfold plaidFtSky mixedFtSky; rw [show ∑ j,_ = ∑ j,(E.weight j:ℂ)*i from Finset.sum_congr rfl (fun j _=> congr_arg _ (he j)),← Finset.sum_mul,← Complex.ofReal_sum,E.total]; simp
lemma pFt_oneSky : (planterFtSky E W).part (quiet _)=1:= by
  change plaidFtSky E (fun j z=> _)=1
  simp_rw [Poly.pass_part _ (un_quietSky E W ..),plaidF_constSky]

-- compare to Wcur only after forecasts paid

def leadFtSky := connected (planterFtSky E W) (pFt_oneSky E W)
end
end YM.Next.Rank.Tapes.West
