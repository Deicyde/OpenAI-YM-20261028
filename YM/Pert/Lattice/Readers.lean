import YM.Pert.Lattice.Rotation
import YM.Labels.Action
import YM.Pert.Lattice.Together
/-! Unsubtracted polynomial columns with physical Taylor-slot engineering factors. Use this reader with separate Wick-subtractions and physical mixing. -/
set_option autoImplicit false
set_option maxRecDepth 3000
noncomputable section
namespace YM.Pert.Bare
open Lattice Function Filter Orb Labels MvPolynomial
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

def valuesU (r h : ℝ) (U : Lattice.Links (Per n) G.El) (x : Site n) : Jet G := fun j => r⁻¹ • tensorJet h U x j
def exactColumn (r h : ℝ) (U : Lattice.Links (Per n) G.El) (x : Site n) : Pol G →ₐ[ℂ] ℂ := Labels.read (valuesU r h U x)
lemma exact_invariant (r h : ℝ) (U : Lattice.Links (Per n) G.El) (x : Site n) (t : Site n→G.El) {d : ℕ} (p : Label G d) :
   exactColumn r h (gauge t U) x p.val = exactColumn r h U x p.val := by
   have e : valuesU r h (gauge t U) x = colored (t x) (valuesU r h U x) := by funext j; simp [valuesU,colored,tensor_gauge]
   have H : p.val∈invariantSpace G := p.property.2
   unfold exactColumn; rw [e]; exact H _ _
lemma exact_tensor (r h : ℝ) (U : Lattice.Links (Per n) G.El) (x : Site n) (s : Signed) (p : Pol G) :
    exactColumn r h (pull s 0 U) x p = exactColumn r h U (affine s 0 x) (Labels.rotated s.ortho p) := by
  have e : valuesU r h (pull s 0 U) x = changedJet (fun j => Labels.Taylor.turn (j:=j) s.ortho⁻¹) (valuesU r h U (affine s 0 x)) := by
    funext j; simp only [valuesU,tensor_move,changedJet,map_smul,show s⁻¹.ortho=s.ortho⁻¹ from Signed.inclusionO.map_inv ..]
  unfold exactColumn; rw [e]; exact Eq.symm (eval_changed ..)

/-- Numerator of one scalar leg, differentiated before slot division. -/
def datum (h : ℝ) (x : Site n) (i : Key G) (a : Potential G n) := Complex.ofReal (((axes G i.1).repr (tensorJet h (positiveLinks a) x i.1)) i.2)
lemma datum_diff (h : ℝ) (x : Site n) (i : Key G) : ContDiffAt ℝ ω (datum h x i) 0 := by
  let L := Complex.ofRealCLM ∘L ((axes G i.1).coord i.2).toContinuousLinearMap
  exact L.contDiff.contDiffAt.comp (0:Potential G n) (tensor_diff ..)
@[simp] lemma datum_flat (h : ℝ) (x : Site n) (i : Key G) : datum h x i 0 = 0 := by simp [datum]
def seriesLex (h : ℝ) (x : Site n) (c : Coords G n) (i : Key G) := PowerSeries.mk (fun e => scaleJet (datum h x i) (e+1) c)
lemma shift_lex (h : ℝ) (x : Site n) (v) (i : Key G) : seriesLex h x v i * PowerSeries.X = PowerSeries.mk (fun e => scaleJet (datum h x i) e v) := by
  ext1 k
  cases k with
  | zero => simp [scaleJet_zero]
  | succ k => simp [PowerSeries.coeff_succ_mul_X,seriesLex]
def field (h : ℝ) (x : Site n) (v : Coords G n) (p : Pol G) : PowerSeries ℂ := MvPolynomial.eval₂Hom PowerSeries.C (seriesLex h x v) p
lemma field_C (z : ℂ) (v : Coords G n) (h x) : field h x v (C z) = PowerSeries.C z := eval₂Hom_C ..
lemma field_add (p q : Pol G) (h : ℝ) (x : Site n) (v) : field h x v (p+q) = field h x v p + field h x v q := map_add (eval₂Hom _ _) _ _
lemma field_mul (p q : Pol G) (h : ℝ) (x : Site n) (v) : field h x v (p*q) = field h x v p * field h x v q := map_mul (eval₂Hom _ _) _ _
lemma field_X (h : ℝ) (x : Site n) (c : Coords G n) (i : Key G) : field h x c (X i) = seriesLex h x c i := by unfold field; exact MvPolynomial.eval₂Hom_X' .. 
lemma field_ready (h : ℝ) (x : Site n) (p : Pol G) : Ready (fun c => field h x c p) := by
  induction p using MvPolynomial.induction_on
  case C z => simp_rw [field_C]; exact Ready.constant _
  case add p q hp hq => simp_rw [field_add]; exact hp.add hq
  case mul_X p i hp => simp_rw [field_mul,field_X]; exact hp.mul (Ready.maker (fun k => tame_scaleJet _ _))

variable {I : Type} [DecidableEq I]
def unscaled (h : ℝ) (x : I→Site n) (p : I→Pol G) (s : Finset I) (c) := ∏ i∈s,field h (x i) c (p i)
lemma unscaled_ready (h : ℝ) (x : I→Site n) (p : I→Pol G) (s : Finset I) : Ready (unscaled h x p s) := by
  convert! (Ready.prod (fun i (_ : i∈s) => field_ready h (x i) (p i))) using 1
  ext1; unfold unscaled; rw [Finset.prod_apply]
def correlate (h : ℝ) (x : I→Site n) (p : I→Pol G) (s : Finset I) := normalize (unscaled h x p s)
lemma correlate_unit (h : ℝ) (x : I→Site n) (s : Finset I) : correlate (G:=G) h x (fun _ => 1) s=1 := by
  unfold correlate; have he : unscaled h x (G:=G) (fun _ => 1) s=1 := funext (fun v => by change (∏ i∈s,field h (x i) v (1 : Pol G))=1; simp only [show ∀ (v : Coords G n) (i : I), field h (x i) v (1:Pol G)=1 from fun _ _ => map_one (eval₂Hom _ _),Finset.prod_const_one])
  rw [he]; exact normalized_unit (G:=G) (n:=n)
structure Insert (G : Gauge) where
  cap : ℕ
  operator : Labels.Label G cap

def Insert.pol (q : Insert G) : Pol G := q.operator.val
def Insert.raiseUp (q : Insert G) (e : ℕ) (h : q.cap ≤ e) : Insert G where
  cap := e
  operator := Labels.raiseLabel G h q.operator
@[simp] lemma Insert.raiseUp_pol (q : Insert G) (e : ℕ) (h : q.cap ≤ e) : (q.raiseUp e h).pol = q.pol := rfl

def many (h : ℝ) (x : I→Site n) (s : Finset I) (p : I→Insert G) := correlate h x (fun i => (p i).pol) s
lemma many_includes (h : ℝ) (x : I→Site n) (s : Finset I) (p : I→Insert G) (q : ℕ) (hp : ∀ i,(p i).cap ≤ q) : many h x s p = many h x s (fun i => (p i).raiseUp q (hp i)) := rfl
end YM.Pert.Bare
