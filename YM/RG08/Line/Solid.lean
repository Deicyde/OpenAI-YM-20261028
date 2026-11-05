import YM.RG08.Line.Complex

/-!
# Abstract use of a completed Hessian. The gauge square cancels from the projected inverse --
do NOT try to replace the covariance by the full unprojected inverse.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Line
open Stationary Function Matrix
open scoped Matrix BigOperators Topology
variable {i j m : Type} [Fintype i] [Fintype j] [Fintype m] [DecidableEq i] [DecidableEq m] [DecidableEq j]
variable (q qi Y : Matrix i i ℝ) (L : Matrix j i ℝ) (r : Matrix i j ℝ) (B : Matrix m m ℝ) (P : Matrix m i ℝ) (s : Matrix i m ℝ)

 omit [DecidableEq m] in
/-- Triangular gauge projection of the joint inverse. `P` is onto the marked full-potential
slice (kernel = gauge generators `r`, no assumption of orthogonal projection). `s` any
analytic section defined on all links, such that q in the joint variables restricted by s is B.
`P*s*x=x` **only** required on the tree slice x. `Y` inverse of completion in *same* Haar/gauge
conventions. No rank, positive definiteness or determinant costs hidden in the conclusion. -/
theorem jointProjection (hQ : Y*(q+L.transpose*L)=1) (hr : q*r=0) (hq : s.transpose*q*s=B)
    (hs : q.transpose=q) (hP : P*r=0) (hv : IsUnit (L*r).det) (ht : q*s*P=q) (x : m→ℝ) (hx : (P*s)*ᵥ x=x) :
    (P*Y*P.transpose) *ᵥ (B *ᵥ x)=x := by
  have he := congr_arg (·*r) hQ
  rw [Matrix.one_mul, Matrix.mul_assoc Y,Matrix.add_mul,hr,zero_add,Matrix.mul_assoc,← Matrix.mul_assoc Y] at he
  have hD : Y*L.transpose=r*(L*r)⁻¹:= by
    nth_rw 1 [← he] -- first?
    rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hv,Matrix.mul_one]
  have hM : P*Y*L.transpose=0 := by rw [Matrix.mul_assoc,hD,←Matrix.mul_assoc,hP,Matrix.zero_mul]
  have hi : P.transpose*s.transpose*q = q := by
    have hu:= congr_arg Matrix.transpose ht
    rw [Matrix.transpose_mul,Matrix.transpose_mul,hs, ← Matrix.mul_assoc] at hu
    exact hu
  have hb := congr_arg (P*·) hQ
  change P*(Y*(q+_*L))=P*1 at hb
  simp only [Matrix.mul_add,← Matrix.mul_assoc,hM,Matrix.zero_mul,add_zero, Matrix.mul_one] at hb
  calc _ = (P*Y*(P.transpose*s.transpose*q)*s)*ᵥ x := by rw [←hq, mulVec_mulVec]; simp only [Matrix.mul_assoc]
       _ = x := by rw [hi,hb,hx]
end YM.RG08.Line
