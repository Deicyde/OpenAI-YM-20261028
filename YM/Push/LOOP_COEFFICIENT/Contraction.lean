import YM.Push.LOOP_COEFFICIENT.ExteriorRules
import YM.Push.LOOP_COEFFICIENT.Wick


/-!
# Wedge homotopy and the closed remainder after one direction
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Set Matrix Lattice Laurent Bloch Exterior Complex
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a : Type} [Fintype a] [DecidableEq a] {r n : ℕ} {η C : ℝ}

def down {a : Type} {r : ℕ} (X : Momentum → Matrix (TypeFace (r+1)) a ℂ) (p : Momentum) := (symbol r p).transpose * X p

omit [Fintype a] [DecidableEq a] in
lemma down_down {X : Momentum → Matrix (TypeFace (r+1+1)) a ℂ} : down (down X) = 0 := by
  ext1 p; rw [down,down,← Matrix.mul_assoc, ← Matrix.transpose_mul, symbol,symbol, d_d, transpose_zero, Matrix.zero_mul]; rfl

def Cycle (X : Momentum → Matrix (TypeFace (r+1)) a ℂ) (η : ℝ) := ∀ p∈ Tube η, down X p = 0

def injectAxis (i : Axis) (X : Momentum → Matrix (TypeFace r) a ℂ) (p : Momentum) := left ℂ r i * divideAxis i X p




def halt (i : Axis) (X : Momentum → Matrix (TypeFace r) a ℂ) (p : Momentum) := of fun j k => if i ∈ j.val then 0 else evalAxis i X p j k


lemma symbol_mask (i : Axis) (p : Momentum) (r) : symbol r p = symbol r (mask i p) + q p i • left ℂ r i := by
  have he : q p = q (mask i p) + Pi.single i (q p i) := by funext b; by_cases h : b=i <;> simp [q,h,mask_apply]
  conv_lhs => rw [symbol,he]
  rw [symbol]; simp [wedge,add_smul,Finset.sum_add_distrib,Pi.single_apply,ite_smul]

variable {X : Momentum → Matrix (TypeFace (r+1)) a ℂ} (hX : Wick X η C (n+1)) (hc : Cycle X η)
include hX hc
lemma down_divided (i : Axis) {p : Momentum} (hp : p ∈ Tube (η/6)) : down (divideAxis i X) p = -((left ℂ r i).transpose * evalAxis i X p) := by
  let E := evalAxis i X
  have hs := tube_mono (show η/6 ≤ η by linarith [hX.side]); have hd := (hX.divideAxis i).smooth p hp
  have he : ContDiffAt ℂ ω (fun p => down (divideAxis i X) p + (left ℂ r i).transpose * E p) p :=
    (analyticMul (analyticTranspose symbol_diff) hd).add (analyticMul contDiffAt_const ((hX.evalAxis i).smooth _ (hs hp)))
  apply eq_neg_of_add_eq_zero_left; ext b c; exact cancel_Q (f:=fun p => (down (divideAxis i X) p + (left ℂ r i).transpose * E p) b c) i (analyticComponent he b c).continuousAt
    (eventually_of_mem ((Work.F07.stripOpen _).mem_nhds hp) (fun p hp => show (q p i • (down (divideAxis i X) p + (left ℂ r i).transpose * E p)) b c = (0:Matrix (TypeFace r) a ℂ) b c by
      have hz := hc _ (mask_tube i (hs hp)); rw [down] at hz
      dsimp only [E]; rw [smul_add,down, ← Matrix.mul_smul, hX.divide_eq i hp,Matrix.mul_sub, show (symbol r p).transpose * X p = 0 from hc p (hs hp),symbol_mask i p r, Matrix.transpose_add,Matrix.transpose_smul, Matrix.add_mul,evalAxis,hz,zero_add, Matrix.smul_mul,zero_sub,neg_add_cancel]))

lemma halt_exact (i : Axis) {p : Momentum} (hp : p∈Tube (η/6)) : down (injectAxis i X) p + halt i X p = X p := by
  let D := divideAxis i X p
  let E := evalAxis i X p
  have he := hX.divide_eq i hp
  have ht := down_divided hX hc i hp
  ext j k
  have h := congr_fun (wedge_dual ℂ (q p) i (D.col k)) j
  change down (injectAxis i X) p j k + (left ℂ r i * down (divideAxis i X) p) j k = (q p i • D) j k at h
  rw [ht,he,Matrix.mul_neg,Matrix.neg_apply,Matrix.sub_apply,show (left ℂ r i * ((left ℂ r i).transpose * evalAxis i X p)) j k = if i∈j.val then E j k else 0 from diag_axis ℂ i j (E.col k)] at h
  simp only [Matrix.add_apply,halt,of_apply]; split <;> simp_all [E,sub_eq_add_neg]

omit hc in
lemma Cycle.halt (i : Axis) (hc : Cycle X η) : Cycle (Loops.halt i X) (η/6) := fun p hp => by
  have he := congr_arg ((symbol r p).transpose * ·) (halt_exact hX hc i hp)
  rw [Matrix.mul_add,show (symbol r p).transpose * down (Loops.injectAxis i X) p = _ from congr_fun (down_down (X:=Loops.injectAxis i X)) p, Pi.zero_apply,zero_add] at he
  exact he.trans (hc p (tube_mono (by linarith [hX.side]) hp))
end YM.Push.Loops
