import YM.Next.FOUNDATIONS.LinkBounds
import YM.Push.LOOP_COEFFICIENT.Chain


/-! # Real covariance in the counting basis -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Lattice Wilson Precision Exterior
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {n m k : Type} [Fintype n] [Fintype m] [Fintype k] [DecidableEq n] [DecidableEq m] [DecidableEq k]
  {A X Y : Matrix n n ℝ} {B : Matrix m m ℝ} {C : Matrix k k ℝ}

def ortho (A : Matrix n n ℝ) := A.transpose * A = 1

def Carries (A : Matrix n n ℝ) (B : Matrix m m ℝ) (X X' : Matrix n m ℝ) := X' * B = A * X

abbrev clm (X : Matrix m n ℝ) : (n → ℝ) →L[ℝ] m → ℝ := X.mulVecLin.toContinuousLinearMap
lemma ortho.rev (h : ortho A) : A * A.transpose = 1 := _root_.mul_eq_one_comm.mp h

lemma ortho.abs_det (h : ortho A) : |A.det| = 1 := by
  have he := congr_arg Matrix.det h
  rw [det_mul,det_transpose,det_one] at he; rw [← abs_one]
  exact abs_eq_abs.mpr (by rcases sq_eq_one_iff.mp (show A.det^2=1 by rwa [pow_two]) with h|h <;> simp [h])

lemma ortho.isUnit (h : ortho A) : IsUnit A := A.isUnit_iff_isUnit_det.mpr
  (isUnit_iff_ne_zero.mpr fun he => by have := h.abs_det; simp [he] at this)

lemma ortho.dot (h : ortho A) (v w : n → ℝ) : (A *ᵥ v) ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ w := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,h,Matrix.one_mulVec]
lemma ortho_of_dot (h : ∀ v w : n → ℝ, (A *ᵥ v) ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ w) : ortho A := by
  apply pairing_ext (Y:=1)
  intro x y; rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,Matrix.vecMul_transpose, h x y, Matrix.one_mulVec]

namespace Carries
variable {P P' : Matrix n m ℝ}
omit [DecidableEq m] in lemma left_eq (h : Carries A B P P') (ha : ortho A) : A.transpose * P' * B = P := by
  rw [Matrix.mul_assoc, show _ = _ from h,← Matrix.mul_assoc, ha,Matrix.one_mul]
omit [DecidableEq m] in lemma from_left (ha : ortho A) (h : A.transpose * P' * B = P) : Carries A B P P' := by
  unfold Carries; rw [← h,← Matrix.mul_assoc,← Matrix.mul_assoc,ha.rev,Matrix.one_mul]

lemma adj (h : Carries A B P P') (ha : ortho A) (hb : ortho B) : Carries B A P.transpose P'.transpose := by
  apply from_left hb
  rw [← h.left_eq ha, transpose_mul, transpose_mul,transpose_transpose,Matrix.mul_assoc]

omit [DecidableEq m] [DecidableEq n] [DecidableEq k] in
lemma mul {M M' : Matrix m k ℝ} (h : Carries A B P P') (hm : Carries B C M M') : Carries A C (P*M) (P'*M') := by
  unfold Carries; rw [Matrix.mul_assoc, show _ = _ from hm, ← Matrix.mul_assoc, show _=_ from h, Matrix.mul_assoc]

omit [DecidableEq m] [DecidableEq n] in
lemma add {M M' : Matrix n m ℝ} (h : Carries A B P P') (hm : Carries A B M M') : Carries A B (P+M) (P'+M') := by
  unfold Carries; rw [Matrix.add_mul,Matrix.mul_add, show _=_ from h,show _=_ from hm]

omit [DecidableEq m] [DecidableEq n] in
lemma smul (h : Carries A B P P') (r : ℝ) : Carries A B (r • P) (r • P') := by unfold Carries; rw [Matrix.mul_smul,Matrix.smul_mul,show _=_ from h]

lemma one : Carries A A 1 1 := by unfold Carries; rw [Matrix.one_mul, Matrix.mul_one]

omit [DecidableEq m] [DecidableEq n] in
lemma sum {ι : Type*} (s : Finset ι) {P P' : ι → Matrix n m ℝ} (h : ∀ i∈s,Carries A B (P i) (P' i)) :
    Carries A B (∑ i∈s,P i) (∑ i∈s,P' i) := by
  unfold Carries; rw [Matrix.mul_sum,Matrix.sum_mul]; exact Finset.sum_congr rfl h

lemma pow (h : Carries A A X Y) (i : ℕ) : Carries A A (X^i) (Y^i) := by
  induction i with
  | zero => rw [pow_zero,pow_zero]; exact one
  | succ _ ih => rw [pow_succ,pow_succ]; exact ih.mul h

lemma det (h : Carries A A X Y) (ha : ortho A) : Y.det = X.det := by
  have he := congr_arg Matrix.det h
  rw [det_mul,det_mul, mul_comm _ A.det] at he
  exact mul_left_cancel₀ ((isUnit_iff_isUnit_det _).mp ha.isUnit).ne_zero he

lemma trace (h : Carries A A X Y) (ha : ortho A) : Y.trace = X.trace := by
  rw [← h.left_eq ha, Matrix.trace_mul_cycle,ha.rev, Matrix.one_mul]

lemma inv (h : Carries A A X Y) (ha : ortho A) : Carries A A X⁻¹ Y⁻¹ := by
  unfold Carries
  by_cases hx : IsUnit X.det
  · have hy : IsUnit Y.det := h.det ha ▸ hx
    rw [show Y⁻¹ * A = Y⁻¹ * A * (X * X⁻¹) by rw [Matrix.mul_nonsing_inv _ hx,Matrix.mul_one],
      ← Matrix.mul_assoc _ X,Matrix.mul_assoc _ _ X,← show _=_ from h,← Matrix.mul_assoc _ Y,
      Matrix.nonsing_inv_mul _ hy, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hx,Matrix.nonsing_inv_apply_not_isUnit _ (h.det ha ▸ hx),Matrix.zero_mul,Matrix.mul_zero]

end Carries

-- Jets tied to actual group arrays by tangent transformations.
lemma invariant_cost {f g : (n → ℝ) → ℝ} (ha : ortho A) (hg : ContDiffAt ℝ ω g 0) (he : g ∘ clm A =ᶠ[𝓝 0] f) :
    Carries A A (bilinearAt f 0) (bilinearAt g 0) := by
  apply Carries.from_left ha (pairing_ext fun x y => ?_)
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    bilinearAt_dotProduct,bilinearAt_dotProduct, ← (he.iteratedFDeriv ℝ 2).self_of_nhds,
    Next.Foundations.jets_linear (clm A) (hg.of_le le_top), ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext i; fin_cases i <;> rfl

omit [DecidableEq n] in
lemma carries_linear {f g : (m → ℝ) → (n → ℝ)} (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0)
    (he : g ∘ clm B =ᶠ[𝓝 0] clm A ∘ f) : Carries A B (linearAt f 0) (linearAt g 0) := by
  have hd := he.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_comp 0 (show DifferentiableAt ℝ g (clm B 0) by simpa only [map_zero] using hg.differentiableAt (by simp)) (clm B).differentiableAt,
    fderiv_comp 0 (clm A).differentiableAt (hf.differentiableAt (by simp)),(clm A).fderiv,(clm B).fderiv,map_zero] at hd
  refine Matrix.ext_iff_mulVec.mpr fun x => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,linearAt_mulVec,linearAt_mulVec]; exact DFunLike.congr_fun hd x

lemma carries_twist {f g : (m → ℝ) → (n → ℝ)} (ha : ortho A) (hb : ortho B) (hf : ContDiffAt ℝ ω f 0)
    (hg : ContDiffAt ℝ ω g 0) (he : g ∘ clm B =ᶠ[𝓝 0] clm A ∘ f) (v : n → ℝ) :
    Carries B B (twist f 0 v) (twist g 0 (A *ᵥ v)) := by
  have hd := (he.iteratedFDeriv ℝ 2).self_of_nhds
  rw [Next.Foundations.jets_linear _ (hg.of_le le_top), (clm A).iteratedFDeriv_comp_left hf le_top] at hd
  apply Carries.from_left hb (pairing_ext fun x y => ?_)
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,
    twist_dotProduct hg,twist_dotProduct hf, ← ha.dot v]
  congr 1
  have hh := DFunLike.congr_fun hd ![x,y]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply] at hh
  refine Eq.trans ?_ hh
  congr 1; ext i; fin_cases i <;> rfl

variable {G : Gauge} {U U' : PatchField G m} {V V' : PatchField G n}

omit [DecidableEq n] [DecidableEq m] in
lemma localize_motion (A : Matrix (Point G n) (Point G n) ℝ) (B : Matrix (Point G m) (Point G m) ℝ)
    {f g : PatchField G m → PatchField G n} (hf : MatDiffAt (f ∘ vary U) 0)
    {φ : PatchField G n → PatchField G n}
    (hi : ∀ᶠ x in 𝓝 (0:Array G m), g (vary U' (B *ᵥ x)) = φ (f (vary U x)))
    (hm : ∀ v, φ (vary (f U) v) = vary (g U') (A *ᵥ v)) :
    localize g U' ∘ clm B =ᶠ[𝓝 0] clm A ∘ localize f U := by
  have ht := ((clm A).contDiff.contDiffAt.comp (f:=localize f U) 0 (localize_diff hf)).continuousAt.tendsto
  rw [Function.comp_apply,localize_zero,map_zero] at ht
  filter_upwards [hi,localized hf,ht.eventually (displacement_vary (g U'))] with x hx hl hd
  change (displacement (g U') (g (vary U' (B *ᵥ x)))) = _
  rw [hx,show f (vary U x) = vary (f U) (localize f U x) from hl,hm]; exact hd
end YM.Push.Loops
