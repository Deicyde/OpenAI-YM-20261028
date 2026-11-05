import YM.Analysis.Polydisc
import YM.Extra.FREE_DETECTOR_ALGEBRA.Aim

set_option warningAsError false

/-! Supply arbitrarily many independent modes at a single derivative order.
Use a complex null direction only to generate *real* homogeneous Taylor
tensors. Coordinates for G.Color unaffected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick  Labels
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

namespace Polar

/-- One null direction; last component left free for F polarization. -/
def axis (t : ℝ) : Axis→ℂ := ![1,(Real.sqrt (1+t^2):ℂ)*Complex.I,(t:ℂ),0]
lemma quad (t : ℝ) : ∑ i : Axis, axis t i * axis t i = 0 := by
  have he : (Real.sqrt (1+t^2))^2 = 1+t^2 := Real.sq_sqrt (by positivity)
  have ht := congr_arg Complex.ofReal he
  simp only [Complex.ofReal_pow, Complex.ofReal_add,Complex.ofReal_one] at ht
  simp [axis,Fin.sum_univ_succ]; linear_combination -ht + (↑(Real.sqrt (1+t^2)) : ℂ)^2 * Complex.I_sq

def phase (t : ℝ) : E4→L[ℝ] ℂ := (LinearMap.toContinuousLinearMap {
  toFun x := ∑ i : Axis,(↑(x i) : ℂ) * axis t i
  map_add' x y := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c y := by simp [Finset.mul_sum,Complex.real_smul,mul_assoc] })
@[simp] lemma phase_basis (a : Axis) (t : ℝ) : phase t (basis a) = axis t a := by
  change ∑ i : Axis, (↑(basis a i):ℂ)*axis t i = _; simp [apply_ite, ite_mul]

def product (j : ℕ) (t : ℝ) : T E4 ℂ j := (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin j) ℂ).compContinuousLinearMap fun _ => phase t
lemma prod_eval (j : ℕ) (t : ℝ) (x : Fin j→E4) : product j t x = ∏ i : Fin j, phase t (x i) := rfl
lemma prod_sym (j : ℕ) (t : ℝ) : Tensor.Sym (product j t) := fun v s => by
  simp_rw [prod_eval,comp_apply]; exact Equiv.prod_comp s (fun i => phase t (v i))

private def e (a : Axis) : ℂ := if a=3 then 1 else 0
private def H (t : ℝ) (a b : Axis) := axis t a * e b - axis t b * e a

def test (j : ℕ) (t : ℝ) : TwoJet ℂ j := fun a b => H t a b • product j t
lemma diag_test (j : ℕ) (t : ℝ) (a b : Axis) (x : E4) : diagonal (test j t a b) x = H t a b * phase t x ^ j := by
  unfold test Tensor.diagonal; simp [prod_eval]

theorem on_axis (j : ℕ) (t : ℝ) : test j t∈onShell ℂ j := by
  let q := axis t
  have he (x : E4) (a b i : Axis) :
      grad a (diagonal (test j t b i)) x = ((j:ℂ)* phase t x^(j-1))* q a * H t b i := by
    rw [funext (diag_test j t b i),grad,D, ((phase t).hasFDerivAt.pow j|>.const_mul (H t b i)).fderiv]
    simp [q]; ring
  constructor
  · constructor
    · intro i b v s; exact congr_arg (fun x : ℂ => H t i b • x) (prod_sym j t v s)
    · intro i b; unfold test; rw [show H t i b = - H t b i from (neg_sub ..).symm]; rw [neg_smul]
    intro i a b x
    simp_rw [he]; unfold H q; ring
  intro b x
  have hp : ∑ i : Axis, q i * H t i b = 0 := by
    unfold H q e
    simp_rw [mul_sub,← mul_assoc,Finset.sum_sub_distrib,← Finset.sum_mul,quad]; simp [mul_ite,axis]
  simp_rw [he,mul_assoc, ← Finset.mul_sum,hp,mul_zero]

/-- Keep only the real part. -/
def realMode (j : ℕ) (t : ℝ) : BareSol j := insertColor Complex.reCLM j ⟨test j t,on_axis j t⟩

private lemma sets (j : ℕ) (i : Fin (j+1)) : ∃ s : Finset (Fin j),s.card=i.val := by
  obtain ⟨s,_,hs⟩ := Finset.exists_subset_card_eq (s:=Finset.univ (α:=Fin j)) (show i.val ≤ Finset.univ.card by
    simp only [Finset.card_univ,Fintype.card_fin]; omega)
  exact ⟨s,hs⟩

/-- Vary order-j direction choices on F03. -/
def taps (j : ℕ) (i : Fin (j+1)) : Module.Dual ℝ (BareSol j) where
  toFun P := P.val 0 3 (fun b => if b ∈ (sets j i).choose then basis 2 else basis 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


end Polar


end YM.Extra.FD
