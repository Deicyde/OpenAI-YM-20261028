import YM.Push.LOOP_COEFFICIENT.Pullback

/-!
# Exact logdet drift difference before taking a mesh limit
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Filter Set Lattice RG Wilson Precision Bloch Exterior
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {m k : Type} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]

abbrev RealTrace (m k : Type) [Fintype m] [Fintype k] [DecidableEq k] := (m → ℝ) →L[ℝ] Matrix k k ℝ

namespace RealTrace
scoped instance : NormedAddCommGroup (RealTrace m k) := ContinuousLinearMap.toNormedAddCommGroup
scoped instance : NormedSpace ℝ (RealTrace m k) := ContinuousLinearMap.toNormedSpace
end RealTrace
open scoped RealTrace

def respLinear (R : (m → ℝ) → RealTrace m k) := (fderiv ℝ R 0).toLinearMap₁₂.flip.compr₂ (Matrix.traceLinearMap k ℝ ℝ)

def respCoeff (R : (m → ℝ) → RealTrace m k) : Matrix m m ℝ := LinearMap.toMatrix₂' ℝ (respLinear R)

def accLinear (R : (m → ℝ) → RealTrace m k) := (((matrixMulLinear k k k ℝ).compl₁₂ (R 0).toLinearMap (R 0).toLinearMap).compr₂ (Matrix.traceLinearMap k ℝ ℝ))

def accCoeff (R : (m → ℝ) → RealTrace m k) : Matrix m m ℝ := LinearMap.toMatrix₂' ℝ (accLinear R)

lemma dual_pairing (B : (m → ℝ) →ₗ[ℝ] (m → ℝ) →ₗ[ℝ] ℝ) (x y : m → ℝ) : x ⬝ᵥ ((LinearMap.toMatrix₂' ℝ B) *ᵥ y) = B x y := by
  rw [← Matrix.toLinearMap₂'_apply']; change ((LinearMap.toMatrix₂' ℝ).symm ((LinearMap.toMatrix₂' ℝ) B) x y : ℝ) = _
  rw [LinearEquiv.symm_apply_apply]

lemma response_pair (R : (m → ℝ) → RealTrace m k) (x y : m → ℝ) : x ⬝ᵥ (respCoeff R *ᵥ y) = (fderiv ℝ R 0 y x).trace := dual_pairing ..
lemma double_pair (R : (m → ℝ) → RealTrace m k) (x y : m → ℝ) : x ⬝ᵥ (accCoeff R *ᵥ y) = (R 0 x * R 0 y).trace := dual_pairing ..
omit [DecidableEq m] in
lemma transpose_pair (X : Matrix m m ℝ) (x y) : x ⬝ᵥ (X.transpose *ᵥ y) = (X *ᵥ x) ⬝ᵥ y := by rw [dotProduct_transpose_mulVec, dotProduct_comm]

variable {R : (m → ℝ) → RealTrace m k} {J : (m → ℝ) → (m → ℝ)} (hr : ContDiffAt ℝ ω R 0) (hj : ContDiffAt ℝ ω J 0) (h0 : J 0 = 0)
include hr
omit [DecidableEq m] in
lemma response_value (x y) : fderiv ℝ (fun b => (R b x).trace) 0 y = (fderiv ℝ R 0 y x).trace := by
  let L := (Matrix.traceLinearMap k ℝ ℝ).toContinuousLinearMap
  have he := (hr.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const x (0:m → ℝ))
  rw [show fderiv ℝ (fun b => (R b x).trace) 0 = _ from (L.hasFDerivAt.comp (0 : m → ℝ) he).fderiv]
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.comp_apply]; rfl

include hj h0
private def aug (R : (m → ℝ) → RealTrace m k) (J : (m → ℝ) → (m → ℝ)) (b : m → ℝ) := 1 + R b (J b)

omit h0 [DecidableEq m] in
private lemma aug_diff : ContDiffAt ℝ ω (aug R J) 0 := contDiffAt_const.add (hr.clm_apply hj)
omit hr hj [DecidableEq m] in
private lemma aug_zero : aug R J 0 = 1 := by rw [aug,h0,map_zero,add_zero]
omit [DecidableEq m] in
private lemma aug_first (v) : fderiv ℝ (aug R J) 0 v = R 0 (fderiv ℝ J 0 v) := by
  have he := ((hr.differentiableAt (by simp)).hasFDerivAt.clm_apply (hj.differentiableAt (by simp)).hasFDerivAt).const_add (1:Matrix k k ℝ)
  rw [show fderiv ℝ (aug R J) 0 = _ from he.fderiv]
  simp [h0]; rfl
omit [DecidableEq m] in
private lemma aug_second (u v) : iteratedFDeriv ℝ 2 (aug R J) 0 ![u,v] = R 0 (fderiv ℝ (fderiv ℝ J) 0 u v) +
    fderiv ℝ R 0 u (fderiv ℝ J 0 v) + fderiv ℝ R 0 v (fderiv ℝ J 0 u) := by
  have hi : ContDiffAt ℝ (2:ℕ) (fun _ : m → ℝ => (1:Matrix k k ℝ)) 0 := contDiffAt_const
  rw [show aug R J = (fun _ => 1) + fun b => R b (J b) from rfl]; erw [iteratedFDeriv_add_apply hi ((hr.clm_apply hj).of_le le_top), _root_.add_apply, iteratedFDeriv_two_apply,
    fderiv_fun_const,fderiv_zero]; change 0 + iteratedFDeriv ℝ 2 (fun b => R b (J b)) 0 ![u,v] = _; rw [zero_add]
  rw [iteratedFDeriv_two_apply]; change fderiv ℝ (fderiv ℝ fun b => R b (J b)) 0 u v = _
  simpa [h0] using! prod_second (ContinuousLinearMap.id ℝ (RealTrace m k)) hr hj u v

variable {F B : (m → ℝ) → Matrix k k ℝ}
lemma drift_equation (hz : ∀ w, (R 0 w).trace=0) (hF : F =ᶠ[𝓝 0] fun b => B b * (1 + R b (J b))) (hB : ContDiffAt ℝ ω B 0) (hb : IsUnit (B 0)) :
    bilinearAt (fun b => Real.log (F b).det) 0 = bilinearAt (fun b => Real.log (B b).det) 0 + ((linearAt J 0).transpose * respCoeff R + (respCoeff R).transpose * linearAt J 0 -
      (linearAt J 0).transpose * accCoeff R * linearAt J 0) := by
  have hd := aug_diff hr hj; have he : aug R J 0 = 1 := aug_zero h0
  have hi := (isUnit_iff_isUnit_det _).mp hb
  have hi' : IsUnit (aug R J 0).det := by rw [he]; simp
  rw [bilinearAt_congr (g:=fun b => Real.log (B b).det + Real.log (aug R J b).det) (by
    filter_upwards [hF,(det_contDiff.contDiffAt.comp 0 hB).continuousAt.eventually_ne hi.ne_zero,
      (det_contDiff.contDiffAt.comp 0 hd).continuousAt.eventually_ne hi'.ne_zero] with x hF hb hx
    rw [hF,Matrix.det_mul]; exact Real.log_mul hb hx), bilinearAt_add (logdet_contDiff hB hi) (logdet_contDiff hd hi')]
  congr 1
  refine pairing_ext (fun x y => ?_)
  rw [bilinearAt_dotProduct,logdet_mixed hd hi',traceFee, aug_first hr hj h0 x,aug_first hr hj h0 y, aug_second hr hj h0 x y,he]
  simp only [inv_one,one_mul,mul_one,trace_add,hz, zero_add, Matrix.sub_mulVec,dotProduct_sub,Matrix.add_mulVec,dotProduct_add,← Matrix.mulVec_mulVec,transpose_pair, double_pair, ← response_pair,linearAt_mulVec]
  rw [dotProduct_comm (respCoeff R *ᵥ x),add_comm]
end YM.Push.Loops
