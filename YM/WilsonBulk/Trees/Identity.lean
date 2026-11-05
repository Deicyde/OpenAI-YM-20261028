import YM.WilsonBulk.Trees.Projection
import YM.Next.STATIONARY.Shape.SoftTransfers

/-!
# Projection of a JAUNT joint inverse

The coordinate projector produces *the* exact covariance at every admitted period,
including the inverse of fullMatrix on that slice. The finite-dimensional statement valid even for
forests not respecting orientation and period. Require actual `S` and tree gap from context or
call `Gap.tree_gap` provider. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Finset Precision Exterior Stationary Audience Matrix FreeResolvent Tree
open scoped Topology BigOperators Matrix Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {η : ℝ}

section algebra
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
lemma cancels (X : Matrix α α ℝ) (U : Matrix α α ℝ) (A : Matrix β α ℝ) (B : Matrix α β ℝ)
    (hX : X.transpose = X) (hU : (X + A.transpose*A)*U=1) (hK : X*B=0) (hA : IsUnit (A*B).det) :
    X * U * X = X := by
  let Y := U*X; have h:(X+A.transpose*A)*Y=X := by
    unfold Y; rw [← Matrix.mul_assoc, hU,Matrix.one_mul]
  rw [Matrix.add_mul,Matrix.mul_assoc (A.transpose)] at h
  have hu : B.transpose * X=0 := by
    simpa [transpose_mul,hX] using congrArg Matrix.transpose hK
  have hs:=congrArg (B.transpose * ·) h
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, hu,Matrix.zero_mul,zero_add] at hs
  have he : (A*B)ᵀ*(A*Y)=0 := by rw [transpose_mul,← Matrix.mul_assoc]; exact hs
  have ht:=congrArg (((A*B)ᵀ)⁻¹ * ·) he
  rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul, Matrix.one_mul, Matrix.mul_zero] at ht
  · rw [ht,Matrix.mul_zero,add_zero] at h; rw [Matrix.mul_assoc]; exact h
  simpa only [det_transpose] using hA
omit [DecidableEq β] in
lemma inverse_quotient (X : Matrix α β ℝ) (Y : Matrix β α ℝ) (K V : Matrix α α ℝ) (U : Matrix β β ℝ)
    (h : X*Y=1) (hK : K*V=1)
    (hu : let T:= X.transpose*K*X; T*U*T=T) : X*U*X.transpose=V := by
  let T:= X.transpose*K*X
  have hT : T*U*T=T := hu; have he : V*K=1:=mul_eq_one_comm.mp hK
  have hx : Yᵀ*Xᵀ=1 := by rw [← transpose_mul,h,Matrix.transpose_one]
  have hr : V*Yᵀ*T=X := by simp only [T]; rw [← Matrix.mul_assoc _ (X.transpose*K),← Matrix.mul_assoc,Matrix.mul_assoc V Yᵀ,hx,Matrix.mul_one,he,Matrix.one_mul] -- ?
  have hg : T*Y*V=X.transpose := by
    rw [show T=_ from rfl,Matrix.mul_assoc (X.transpose*K),h,Matrix.mul_one,Matrix.mul_assoc,hK,Matrix.mul_one]
  calc
    _ = V*Yᵀ*(T*U*T)*Y*V := by simp only [← Matrix.mul_assoc,hr]; rw [← hg]; simp only [Matrix.mul_assoc]
    _ = V := by rw [hT,hr,h,Matrix.one_mul]
end algebra
lemma unroll_inverse {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (X : α ≃ β) {M : Matrix α α ℝ} {W : Matrix β β ℝ}
    (h : repackM X X M * W=1) : M * repackM X.symm X.symm W=1 := by
  -- repack_multiply e g (u:=?) etc
  have hg:= congrArg (repackM X.symm X.symm) h
  rw [repack_multiply _ X.symm] at hg
  simpa [repackM] using hg

lemma driven (t : S.Choices) (T : Forest S.ratio) (B : Bed) (P : Clip) (a b : ℝ) (hb : Floor B P f a b)
    (ha : 0<a) (hS : Bid.Larger (G:=G) S)
    (I : Matrix (Co c (ParcelG G S.patch.L)) (Co c (ParcelG G S.patch.L)) ℝ)
    (hI : completedM G B S t * I=1) :
    covariance G S T B.metric =
      let X := (clothe G S).symm
      casting G S T * repackM X X I * (casting G S T).transpose := by
  classical
  let X := (clothe G S).symm
  let J:= postroom (G:=G) S t (inch S.patch.L)
  let A:=frontR G S B
  let Y:=repackM X X I
  have h : (A+Jᵀ*J)*Y=1 := unroll_inverse (clothe G S) hI -- deq
  have hg : Gap (B.metric.acts f) a := ⟨fun v=> (hb.uniform.1 v).1⟩
  have he: treeMatrix G S T B.metric*treeInverse G S T B.metric 0=1 := by
     simpa using! (tree_laws T B.metric hS ha hg (le_refl 0)).2
  let L:= casting G S T; let M:=toActive G S T
  have hx : A=Mᵀ*treeMatrix G S T B.metric*M := to_Gram B T hb.symmetric.1
  have hy : Aᵀ=A := by
    unfold A frontR posting; simp [hb.symmetric.1,power_sym,Matrix.mul_assoc]
  have hv : A*Y*A=A := cancels A Y J (spreadM (G:=G) S) hy h (lie_kernel G S B) (by
    unfold J; erw [fired S t hS.1]; exact fund_det (grenade_safe _ (inch_pos _)))
  rw [hx] at hv
  have ht := inverse_quotient M _ _ _ Y (extend_active G T) he hv
  rw [covariance, ← ht]
  dsimp only [Y,M]; rw [recast]; simp only [transpose_mul, Matrix.mul_assoc, reduce,X]
end YM.WilsonBulk
