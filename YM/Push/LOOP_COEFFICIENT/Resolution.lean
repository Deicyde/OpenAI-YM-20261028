import YM.Push.LOOP_COEFFICIENT.DoubleLift
import YM.Push.LOOP_COEFFICIENT.Wick

/-!
# Real, color-independent scalar two-form resolution of a Signature residual

Precision normalization (take HALF this row for action atoms). Reality after
the identity; no unsigned-only or parity symmetrization of individual legs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Set Matrix Lattice Laurent Bloch Exterior Complex
open scoped Topology Matrix.Norms.L2Operator BigOperators ContDiff ComplexConjugate
variable {G : Gauge} {η C : ℝ} {V : Momentum → Matrix (Axes G) (Axes G) ℂ}

def fiberTape (a : G.ColorIndex) (V : Momentum → Matrix (Axes G) (Axes G) ℂ) (p : Momentum) :=
    (V p).submatrix (fun i => (axisEquiv.symm i,a)) (fun j => (axisEquiv.symm j,a))










variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def realRow (X : Momentum → Matrix a b ℂ) : Row a b := fun i j z => (market (fun p => X p i j) 0 z).re
variable {X : Momentum → Matrix a b ℂ} (hX : Wick X η C 2)
include hX
private def recoveryPrice (η C : ℝ) := C*(2*((1+η/3)/(η/3)))^(Fintype.card Axis)
omit [DecidableEq a] in
private lemma price_market (i j) : Width (η/3) (recoveryPrice η C) (market (fun p => X p i j) 0) := (hX.vane i j).issues (fun p hp => (hX.estimate p hp).entry i j) _ _ (by linarith [hX.side]) (by linarith [hX.side]) (by linarith [hX.side])
omit [DecidableEq a] in lemma realRow_price : (realRow X).strip (η/3) (recoveryPrice η C) := fun i j => Work.F07.widthRealPart (price_market hX i j)
omit [DecidableEq a] in lemma realRow_apply (p : Momentum) (hp : star p=p) : (realRow X).read p = (1/2:ℂ) • (X p + (X (-p)).map conj) := by
  ext i j; unfold realRow; rw [Row.read,Matrix.of_apply,Work.F07.readRealPart (price_market hX i j) (by linarith [hX.side]) hp, (hX.vane i j).paints (fun z hz => (hX.estimate z hz).entry i j) p (Work.F07.realStrip _ hX.side hp),
    (hX.vane i j).paints (fun z hz => (hX.estimate z hz).entry i j) (-p) (Work.F07.realStrip _ hX.side (by rw [star_neg,hp]))]; simp; ring
omit [DecidableEq a] in lemma realRow_zero (i j) : HasSum ((realRow X) i j) 0 ∧ ∀ d : Axis, HasSum (fun z => ((realRow X) i j z) * (z d:ℝ)) 0 := by
  let u := market (fun p => X p i j) 0
  have hσ : 0<η/3 := by linarith [hX.side]
  have hu := price_market hX i j
  have hm := (hX.vane i j).paints (fun z hz => (hX.estimate z hz).entry i j)
  have h0 := Work.F07.realStrip η hX.side (star_zero (R:=Momentum))
  have he : Laurent.read u =ᶠ[𝓝 0] fun p => X p i j := eventually_of_mem ((Work.F07.stripOpen _).mem_nhds h0) hm
  have hz (d) := hX.order (unitAxis d) i j 1 (by decide)
  have hz' d := readJetC hσ (c:=u) hu d
  simp_rw [← line_congr he,lineD,iteratedDeriv_one,fun i => (hz' i).deriv,mul_eq_zero,I_ne_zero,false_or] at hz
  have h0 : ∑' z,u z = 0 := by simpa only [line_zero,← he.self_of_nhds,Laurent.read,mode_constant,one_smul] using hX.order 0 i j 0 (by decide)
  exact ⟨by simpa only [realRow,Complex.ofReal_zero] using! Complex.reCLM.hasSum (show HasSum u 0 from by rw [← h0]; exact (hu.summable hσ.le).hasSum),fun d => by
    have hv : HasSum (fun z : Cover => (z d:ℂ)*u z) 0 := by rw [← hz d]; exact (readMomentC_summable hσ hu d).hasSum
    have h := Complex.reCLM.hasSum hv
    simpa [realRow,Complex.mul_re,u,mul_comm] using h⟩

omit hX



structure Resolves (V : Momentum → Matrix (Axes G) (Axes G) ℂ) (a : G.ColorIndex) (R : Row (TypeFace 2) (TypeFace 2)) : Prop where
  apply (p) : star p = p → dOut (dIn R.read) p = fiberTape a V p
  zero i j : HasSum (R i j) 0 ∧ ∀ d : Axis, HasSum (fun z => R i j z * (z d:ℝ)) 0


end YM.Push.Loops
