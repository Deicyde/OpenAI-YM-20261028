import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Analysis.Polydisc
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Extra.FREE_DETECTOR_ALGEBRA.LegAct
import YM.Extra.FREE_DETECTOR_ALGEBRA.Removal
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04
import YM.Work.G07.Stencil


set_option warningAsError false

/-!
# Physical probe symbols, rotation and contraction

No scale factors on `digit` other than those in `dualSol`: Taylor and Frobenius
as throughout. `barPol` conjugates ordinary complex coefficients. The
coefficient sign for opposite curls is already in `extractVar`'s entry.
No contractions here assumed positive.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Maxwell Wick Pair Labels
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {G : Gauge} {j l n : ℕ} {x y : E4}

/-- Conjugate a Wick polynomial (real form of the jet). -/
def barPol : WickPol G →+* WickPol G := MvPolynomial.map (starRingEnd _)

@[simp] lemma eval_bar (P : WickPol G) (S : TaylorTower G) : probe S (barPol P) = star (probe S P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [barPol,probe]
  | add p q hp hq => simp only [_root_.map_add,hp,hq,star_add]
  | mul_X p i hp => rw [_root_.map_mul,_root_.map_mul,hp,_root_.map_mul]; simp [barPol,probe,Maxwell.coord]

def pullSol (s : Ortho) : WickPol G →ₐ[ℂ] WickPol G :=
  MvPolynomial.aeval fun i => symbol i.fst ((coordinateLeg i).comp (solO s⁻¹).toLinearMap)

def twist (s : Ortho) (A : TaylorTower G) : TaylorTower G := fun j => solO s (A j)

@[simp] lemma pull_eval (s : Ortho) (A : TaylorTower G) (p : WickPol G) : probe A (pullSol s p) = probe (twist s⁻¹ A) p := by
  have h : (probe A).comp (pullSol s) = probe (twist s⁻¹ A) := by
    ext i; rw [AlgHom.comp_apply,pullSol,MvPolynomial.aeval_X,symbol_test,probe,MvPolynomial.aeval_X]; rfl
  exact DFunLike.congr_fun h p

@[simp] theorem pull_mul (s r : Ortho) (P : WickPol G) : pullSol (s*r) P = pullSol s (pullSol r P) := by
  apply equalPol; intro A; simp only [pull_eval,mul_inv_rev]
  apply congr_arg (fun X => probe X P)
  funext i
  exact solAct_mul r⁻¹ s⁻¹ _

@[simp] theorem pull_one (p : WickPol G) : pullSol 1 p = p := by
  apply equalPol; intro X; rw [pull_eval,inv_one,show twist 1 X = X from funext fun _ => solAct_id _]

@[simp] theorem pull_bar (s : Ortho) (P : WickPol G) : pullSol s (barPol P) = barPol (pullSol s P) :=
  equalPol _ _ (by intro A; simp)

/-- Single-order symbols -/
def digit (P : Sol G.Color j) : WickPol G := symbol j (dualSol G.Color j P)

lemma digit_read (P : Sol G.Color j) (A : TaylorTower G) : probe A (digit P) = (dotF P.val (A j).val : ℂ) := symbol_test ..

@[simp] lemma digit_bar (P : Sol G.Color j) : barPol (digit P) = digit P := equalPol _ _ (by intro A; simp [digit_read])

lemma pull_digit (P : Sol G.Color j) (s : Ortho) : pullSol s (digit P) = digit (solO s P) := by
  apply equalPol; intro A
  rw [pull_eval,digit_read,digit_read]
  have he := carry_dot s P.val ((twist s⁻¹ A j).val)
  have h : solAct s (solAct s⁻¹ (A j)) = (A j) := by simp [← solAct_mul]
  have hh : carry s ((twist s⁻¹ A j).val) = (A j).val := congr_arg Subtype.val h

  rw [hh] at he
  exact congr_arg (fun a : ℝ => (a : ℂ)) he.symm

def rCoeff (i : Slot G) : Sol G.Color i.fst := (dualSol G.Color _).symm (coordinateLeg i)

@[simp] lemma digit_coeff (i : Slot G) : digit (rCoeff i) = MvPolynomial.X i := by
  rw [digit,rCoeff,LinearEquiv.apply_symm_apply,symbol_coordinate]

lemma digit_add (P Q : Sol G.Color j) : digit (P+Q) = digit P + digit Q := by
  apply equalPol; intro A; simp only [digit_read,_root_.map_add]
  change ((dotF (P.val+Q.val) _ : ℝ) : ℂ) = _
  rw [_root_.map_add,LinearMap.add_apply,Complex.ofReal_add]

lemma digit_smul (P : Sol G.Color j) (t : ℝ) : digit (t • P) = (t:ℂ) • digit P := by
  apply equalPol; intro A; rw [digit_read,_root_.map_smul,digit_read]
  change ((dotF (t • P.val) _ : ℝ) : ℂ) = _
  rw [_root_.map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; rfl

/-- Opposite-site Wick derivation induced by the symbol. -/
def descend (P : Sol G.Color j) (x y : E4) : Derivation ℂ (WickPol G) (WickPol G) :=
    ∑ i : Fin (legDim G j), (dualSol _ _ P (frame G j i) : ℂ) • Pair.extractVar ⟨j,i⟩ x y

lemma deriv_apply_sum {ι : Type*} (s : Finset ι) (D : ι → Derivation ℂ (WickPol G) (WickPol G)) (x : WickPol G) :
    (∑ i ∈ s,D i) x = ∑ i ∈ s, D i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s h ih => simp [h,ih]

lemma descend_relation (P : Sol G.Color j) (x : Points n) (i : Fin n) (hx : x∈conf n) (W : Fin n → WickPol G) :
    Pair.replace x W i (W i * digit P) = ∑ k : Others i, Pair.replace x W k (descend P (x i) (x k) (W k)) := by
  simp only [digit,symbol,MvPolynomial.C_mul',Finset.mul_sum,_root_.map_sum,
    Algebra.mul_smul_comm, _root_.map_smul, descend,deriv_apply_sum,Derivation.smul_apply,remove x hx]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]

lemma expr_coords (p : Probe G j) : p = ∑ i : Fin (legDim G j), p (frame G j i) • coordinateLeg ⟨j,i⟩ := by
  apply LinearMap.ext; intro S
  conv_lhs => rw [← (frame G j).sum_repr S]
  simp only [_root_.map_sum, _root_.map_smul]
  let F (i : Fin (legDim G j)) : Probe G j := coordinateLeg ⟨j,i⟩
  have he := LinearMap.sum_apply Finset.univ (fun i => p (frame G j i) • F i) S
  refine Eq.trans ?_ he.symm
  exact Finset.sum_congr rfl fun i _ => mul_comm ((frame G j).repr S i) (p (frame G j i))

lemma descend_X (P : Sol G.Color j) (a : Slot G) (hx : x≠y) :
    descend P x y (MvPolynomial.X a) = MvPolynomial.C (legKernel (G:=G) (dualSol _ _ P) (coordinateLeg a) (x-y) : ℂ) := by
  have ht : x-y∈away := sub_ne_zero.mpr hx
  let p := dualSol G.Color _ P
  simp_rw [descend,deriv_apply_sum,Derivation.smul_apply,Pair.extractVar,MvPolynomial.mkDerivation_X]
  change _ = MvPolynomial.C (pairing (G:=G) ht p (coordinateLeg a) : ℂ)
  conv_rhs => rw [expr_coords p]
  simp only [_root_.map_sum, _root_.map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Complex.ofReal_sum,Complex.ofReal_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [MvPolynomial.C_mul,MvPolynomial.C_mul']; rfl

lemma descend_digit (P : Sol G.Color j) (Q : Sol G.Color l) (hx : x≠y) :
    descend P x y (digit Q) = MvPolynomial.C (legKernel (G:=G) (dualSol _ _ P) (dualSol _ _ Q) (x-y) : ℂ) := by
  have ht : x-y∈away := sub_ne_zero.mpr hx
  simp only [digit,symbol,MvPolynomial.C_mul', _root_.map_sum, Derivation.map_smul, descend_X _ _ hx]
  change _ = MvPolynomial.C (pairing (G:=G) ht (dualSol _ _ P) (dualSol _ _ Q) : ℂ)
  conv_rhs => rw [expr_coords (dualSol G.Color l Q)]
  simp only [_root_.map_sum, _root_.map_smul, Complex.ofReal_sum, smul_eq_mul, Complex.ofReal_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [MvPolynomial.C_mul,MvPolynomial.C_mul']; rfl
end YM.Extra.FD
