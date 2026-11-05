import YM.Push.LOOP_COEFFICIENT.Chain
import YM.Push.LOOP_COEFFICIENT.LogDet
import YM.Push.LOOP_COEFFICIENT.Polar


/-!
# Product, inversion and log-determinant identities for real matrices complexified
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Set Matrix Bloch
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {e m n k l : Type}

def cmat : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℂ := Complex.ofRealCLM.toLinearMap.mapMatrix
lemma cmat_apply (M : Matrix m n ℝ) : cmat M = approached M := rfl
variable [Fintype m] [Fintype n] [Fintype k] [Fintype l] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq n] in
lemma cmat_mul (M : Matrix m k ℝ) (N : Matrix k l ℝ) : cmat (M * N) = cmat M * cmat N := Bloch.prom_mul M N

@[simp] lemma cmat_one : cmat (1 : Matrix m m ℝ) = 1 := Complex.ofRealHom.mapMatrix.map_one

lemma cmat_unit {M : Matrix m m ℝ} (h : IsUnit M) : IsUnit (cmat M) := h.map Complex.ofRealHom.mapMatrix

lemma cmat_inv {M : Matrix m m ℝ} (h : IsUnit M) : cmat M⁻¹ = (cmat M)⁻¹ :=
  (Matrix.inv_eq_right_inv (by rw [← cmat_mul,M.mul_nonsing_inv (M.isUnit_iff_isUnit_det.mp h), cmat_one])).symm

omit [DecidableEq m] in
lemma cmat_trace (M : Matrix m m ℝ) : (cmat M).trace = (M.trace : ℂ) := by simp [cmat_apply,approached, Matrix.trace]

omit [DecidableEq n] in
lemma cvec_dot (v w : n → ℝ) : cvec v ⬝ᵥ cvec w = ((v ⬝ᵥ w : ℝ) : ℂ) := by simp [dotProduct,cvec]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
lemma cmat_mulVec (M : Matrix m n ℝ) (v : n → ℝ) : cmat M *ᵥ cvec v = cvec (M *ᵥ v) := funext fun _ => cvec_dot ..

def actualMatrix (f : (m → ℝ) → Matrix n k ℝ) : Jet m (Matrix n k ℂ) := actual cmat f

def actualScalar (f : (m → ℝ) → ℝ) : Jet m ℂ := actual Complex.ofRealAm.toLinearMap f

def matrixMulLinear (m n k 𝕜 : Type) [Fintype n] [Field 𝕜] : Matrix m n 𝕜 →ₗ[𝕜] Matrix n k 𝕜 →ₗ[𝕜] Matrix m k 𝕜 :=
  LinearMap.mk₂ 𝕜 (· * ·) Matrix.add_mul Matrix.smul_mul Matrix.mul_add (fun a b c => Matrix.mul_smul b a c)

def matrixMulCLM (m n k : Type) [Fintype m] [Fintype n] [Fintype k] : Matrix m n ℝ →L[ℝ] Matrix n k ℝ →L[ℝ] Matrix m k ℝ :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp (matrixMulLinear m n k ℝ)).toContinuousLinearMap

omit [DecidableEq n] in
lemma actualMatrix_mul {f : (m → ℝ) → Matrix n k ℝ} {g : (m → ℝ) → Matrix k l ℝ} (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) :
    actualMatrix (fun v => f v * g v) = Jet.bilin (matrixMulLinear n k l ℂ) (actualMatrix f) (actualMatrix g) :=
  actual_bilin (E:= Matrix n k ℂ) (F:=Matrix k l ℂ) (K:=Matrix n l ℂ) cmat cmat cmat (matrixMulCLM n k l) (matrixMulLinear n k l ℂ) hf hg cmat_mul

namespace Jet

/-- Formal inverse jet. Its correctness for actual derivatives requires a nonsingular base. -/
def reciprocal (J : Jet m (Matrix n n ℂ)) : Jet m (Matrix n n ℂ) :=
  let C := Jet.const J.base⁻¹
  let H : Jet m (Matrix n n ℂ) := ⟨0,J.lin,J.quad⟩
  let T := bilin (matrixMulLinear n n n ℂ)
  C.add <| (T (T (C.push (-LinearMap.id)) H) C).add <| T (T (T (T C H) C) H) C

omit [Fintype m] [DecidableEq m] in
lemma reciprocal_lin (J : Jet m (Matrix n n ℂ)) (x) :
    J.reciprocal.lin x = -(J.base⁻¹ * J.lin x * J.base⁻¹) := by
  simp [reciprocal, Jet.add, matrixMulLinear, Jet.push, Jet.const, Jet.bilin]

omit [Fintype m] [DecidableEq m] in
lemma reciprocal_quad (J : Jet m (Matrix n n ℂ)) (x y) :
    let C := J.base⁻¹
    J.reciprocal.quad x y = -(C * J.quad x y * C) + C * J.lin x * C * J.lin y * C + C * J.lin y * C * J.lin x * C := by
  simp [reciprocal, Jet.add, Jet.bilin, matrixMulLinear, Jet.push, Jet.const, add_assoc]
end Jet

lemma actualMatrix_inv {f : (m → ℝ) → Matrix n n ℝ} (hf : ContDiffAt ℝ ω f 0) (h : IsUnit (f 0)) :
    actualMatrix (fun v => (f v)⁻¹) = (actualMatrix f).reciprocal := by
  let g := fun v => (f v)⁻¹
  have hg : ContDiffAt ℝ ω g 0 := (inv_contDiffAt _ ((f 0).isUnit_iff_isUnit_det.mp h)).comp 0 hf
  have h1 : (fun v => f v * g v) =ᶠ[𝓝 0] fun _ => (1:Matrix n n ℝ) := by
    filter_upwards [(det_contDiff.contDiffAt.comp (f:=f) 0 hf).continuousAt.eventually (isOpen_ne.mem_nhds ((f 0).isUnit_iff_isUnit_det.mp h).ne_zero)] with x hx
    exact (f x).mul_nonsing_inv (isUnit_iff_ne_zero.mpr hx)
  have hJ := actual_congr cmat h1
  change actualMatrix _ = _ at hJ
  rw [actualMatrix_mul hf hg, actual_const] at hJ
  let F := actualMatrix f
  let H := actualMatrix g
  have h0 : H.base = F.base⁻¹ := cmat_inv h
  have hc : F.base⁻¹ * F.base = 1 := F.base.nonsing_inv_mul (F.base.isUnit_iff_isUnit_det.mp (cmat_unit h))
  have he (x) : F.base * H.lin x = -(F.lin x * F.base⁻¹) := eq_neg_of_add_eq_zero_left (by rw [← h0]; exact congr_arg (fun x' => x'.lin x) hJ)
  have hli (x) : H.lin x = -(F.base⁻¹ * F.lin x * F.base⁻¹) := by
    have hq := congr_arg (F.base⁻¹ * ·) (he x); rwa [← mul_assoc, hc, one_mul,mul_neg,← mul_assoc] at hq
  apply Jet.ext
  · simpa [Jet.reciprocal, Jet.add, Jet.const,Jet.bilin, matrixMulLinear,Jet.push, F, H] using! h0
  · exact LinearMap.ext fun x => (hli x).trans (F.reciprocal_lin x).symm
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  have eq := congr_arg (fun x' => x'.quad x y) hJ
  change F.base * H.quad x y + F.lin x * H.lin y + F.lin y * H.lin x + F.quad x y * H.base = 0 at eq
  have hz := congr_arg (F.base⁻¹ * ·) eq
  rw [Jet.reciprocal_quad]; change H.quad x y = _
  rw [mul_add,mul_add,mul_add,← mul_assoc _ F.base, hc,one_mul,mul_zero,h0,hli x,hli y,mul_neg,mul_neg,mul_neg,mul_neg] at hz
  simp only [← mul_assoc] at hz
  rw [eq_neg_of_add_eq_zero_left hz |> eq_sub_of_add_eq |> eq_sub_of_add_eq]; abel

omit [DecidableEq n] in
lemma actualMatrix_pre [Fintype e] [DecidableEq e] {f : (e → ℝ) → Matrix n k ℝ} (hf : ContDiffAt ℝ ω f 0) (M : Matrix e m ℝ) :
    actualMatrix (fun v => f (M *ᵥ v)) = (actualMatrix f).pre (cmat M).mulVecLin :=
  actual_pre cmat hf (L:=M.mulVecLin.toContinuousLinearMap) (T:=(cmat M).mulVecLin) (fun v => (cmat_mulVec M v).symm)

lemma actualScalar_quad (f : (m → ℝ) → ℝ) (x y) :
    (actualScalar f).quad x y = x ⬝ᵥ (cmat (bilinearAt f 0) *ᵥ y) := by
  rw [← Matrix.toLinearMap₂'_apply',show (actualScalar f).quad = _ from complex_ext₂ (L:=(actualScalar f).quad) ?_]
  intro v w
  rw [actualScalar, actual_mixed, ← bilinearAt_dotProduct, Matrix.toLinearMap₂'_apply', cmat_mulVec,cvec_dot]; rfl

def logVariation (F : Jet m (Matrix n n ℂ)) : CSpace m →ₗ[ℂ] CSpace m →ₗ[ℂ] ℂ :=
  let H := matrixMulLinear n n n ℂ
  let K := (H F.base⁻¹).comp F.lin
  (F.quad.compr₂ (H F.base⁻¹) - H.compl₁₂ K K).compr₂ (Matrix.traceLinearMap _ ℂ _)

omit [Fintype m] [DecidableEq m] in
lemma logVariation_apply (F : Jet m (Matrix n n ℂ)) (x y) :
    logVariation F x y = (F.base⁻¹ * F.quad x y).trace - (F.base⁻¹ * F.lin x * F.base⁻¹ * F.lin y).trace := by
  change (_ - ((F.base⁻¹ * F.lin x) * (F.base⁻¹ * F.lin y))).trace = _
  rw [trace_sub,← mul_assoc]; rfl

lemma actualScalar_log {f : (m → ℝ) → Matrix n n ℝ} (hf : ContDiffAt ℝ ω f 0) (h : IsUnit (f 0)) :
    (actualScalar (fun v => Real.log (f v).det)).quad = logVariation (actualMatrix f) := by
  refine complex_ext₂ fun v w => ?_
  rw [actualScalar,actual_mixed,logVariation_apply,actualMatrix,actual_mixed,actual_real₁,actual_real₁,logdet_mixed hf ((f 0).isUnit_iff_isUnit_det.mp h)]
  dsimp only [actual]; rw [← cmat_inv h,← cmat_mul,← cmat_mul,← cmat_mul,← cmat_mul,cmat_trace,cmat_trace]
  change ((traceFee .. : ℝ) : ℂ) = _
  rw [traceFee, Complex.ofReal_sub]; rfl
end YM.Push.Loops
