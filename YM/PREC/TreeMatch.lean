import YM.PREC.FrameResponse

/-!
# Tree stationary quadratic gluing

Given REAL counting matrix solve on EVERY torus. `extracted` slice tangent
response rooted at actual projected block. No quotient by harmonic directions.
The stationary quadratic value is a real theorem on these algebraic inputs;
must identify K,H etc and the near-flat germ before it proves any physics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Precision
open Lattice Wilson RG Matrix Exterior Finset Tree
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {c f : Side} {S : StepData c f}

def marked (F : Forest S.ratio) (a : form 1 f) : Prop := ∀ i∈F.trunks,a (i.1,coord i.2)=0

/-- phi formula: hike is BACKWARDS to root, so plus here. -/
def straighten (S : StepData c f) (F : Forest S.ratio) (W : Matrix (Body 1 f) (Body 1 c) ℝ) :
    Matrix (Body 0 f) (Body 1 c) ℝ := LinearMap.toMatrix'
      ((LinearMap.pi fun i : Body 0 f =>
        integralLink i.1 (F.hike i.1)-((LinearMap.proj ((S.ratio.parent i.1),vac)).comp (fixRoot S).mulVecLin)).comp W.mulVecLin)

def extracted (S : StepData c f) (F : Forest S.ratio) (W : Matrix (Body 1 f) (Body 1 c) ℝ) :
    Matrix (Body 1 f) (Body 1 c) ℝ := W+d 0 f*straighten S F W

variable (F : Forest S.ratio) (W : Matrix (Body 1 f) (Body 1 c) ℝ) (a : form 1 c)

lemma books (i : Body 0 f) :
    (straighten S F W *ᵥ a) i=integralLink i.1 (F.hike i.1) (W *ᵥ a)-(fixRoot S *ᵥ (W *ᵥ a)) (S.ratio.parent i.1,vac) := by
  rw [straighten,LinearMap.toMatrix'_mulVec]; rfl

lemma centers : centered S (straighten S F W *ᵥ a) = -(fixRoot S *ᵥ (W *ᵥ a)) := by
  funext ⟨x,i⟩; rw [vac_only i]; simp only [centered,books,Pi.neg_apply]
  rw [S.ratio.embed_parent, Forest.hike, dif_neg (by simp [Tree.leaf,Ratio.embed_parent])]
  simp [integralLink, linkSum]

lemma stays : marked (S:=S) F (extracted S F W *ᵥ a) := by
  rintro i hi
  obtain ⟨x,hx,rfl⟩ := (F.trunk_mem_iff _).mp hi
  have HH := F.stays x hx
  let b := x+(F.up x).vec
  let y := W *ᵥ a
  let p := straighten S F W *ᵥ a
  have ht : integralLink x (F.hike x) y=(if (F.up x).neg then -y ((F.up x).used x |>.1,coord ((F.up x).used x).2) else y ((F.up x).used x |>.1,coord ((F.up x).used x).2)) + integralLink b (F.hike b) y := by
    rw [Forest.hike,dif_pos hx]; rfl
  rw [extracted,add_mulVec,← mulVec_mulVec,Pi.add_apply, d_sites]
  cases h : F.up x with
  | mk i val =>
    rw [h] at HH
    unfold b at ht; rw [h] at ht
    cases val
    · simp only [Step.used,Bool.false_eq_true,↓reduceIte] at *
      simp_rw [books]; change S.ratio.parent (x+step i)=S.ratio.parent x at HH
      change integralLink _ _ (W *ᵥ a)=_ at ht
      rw [HH]; simp only [Step.vec,Bool.false_eq_true,↓reduceIte,y] at ht; linarith only [ht]
    simp only [Step.used,↓reduceIte,sub_add_cancel] at *
    have hh' : (Step.vec ⟨i,true⟩ : Site f) = -step i := rfl
    rw [hh',← sub_eq_add_neg] at HH ht
    simp_rw [books]; rw [HH]; unfold y at ht; linarith only [ht]

section trace

variable (H : Matrix (Body 2 f) (Body 2 f) ℝ) (H' : Matrix (Body 2 c) (Body 2 c) ℝ)

def K {n : Side} (H : Matrix (Body 2 n) (Body 2 n) ℝ) : Matrix (Body 1 n) (Body 1 n) ℝ :=
    (d 1 n).transpose*H*d 1 n

lemma d_d_vac : d 1 c*d 0 c=0 := closed 0 c
lemma K_kills : K H' * d 0 c=0 := by rw [K,Matrix.mul_assoc,d_d_vac,Matrix.mul_zero]
lemma K_orthogonal : (d 0 c).transpose*K H'=0 := by
  rw [K,← Matrix.mul_assoc,← Matrix.mul_assoc, ← Matrix.transpose_mul, d_d_vac]; simp

structure Inputs (S : StepData c f) (W : Matrix (Body 1 f) (Body 1 c) ℝ) (H : Matrix (Body 2 f) (Body 2 f) ℝ)
    (H' : Matrix (Body 2 c) (Body 2 c) ℝ) : Prop where
  primal : K H*W=(mean S).transpose*K H'
  dual : mean S*W=1-S.kernel.penalty⁻¹ • K H'

lemma stationed (i : Inputs S W H H') :
    probe S*extracted S F W=1-S.kernel.penalty⁻¹ • K H' ∧
    K H*extracted S F W = (probe S).transpose*K H' := by
  constructor
  · rw [← i.dual]
    apply Matrix.toLin'.injective
    apply LinearMap.ext; intro x
    change (probe S*extracted S F W) *ᵥ x=(mean S*W) *ᵥ x
    rw [← mulVec_mulVec,extracted, add_mulVec,← mulVec_mulVec, mulVec_add, root_gradient, centers, mulVec_neg,probe, add_mulVec, ← mulVec_mulVec, add_neg_cancel_right, mulVec_mulVec]
  rw [extracted, Matrix.mul_add, ← Matrix.mul_assoc _ (d 0 f), K_kills]; rw [Matrix.zero_mul, add_zero]
  rw [probe, transpose_add, Matrix.add_mul,i.primal,transpose_mul,Matrix.mul_assoc, K_orthogonal,Matrix.mul_zero,add_zero]

lemma action (i : Inputs S W H H') :
    let T:=extracted S F W
    let P:=1-probe S*T
    T.transpose*K H*T+S.kernel.penalty • (P.transpose*P)=K H' := by
  intro T P
  have hv : P = S.kernel.penalty⁻¹ • K H' := by unfold P T; rw [(stationed F W H H' i).1]; simp
  calc
    _ = T.transpose*(probe S).transpose*K H'+ P.transpose*(S.kernel.penalty • P) := by
      rw [Matrix.mul_assoc _ (K H) T,← Matrix.mul_smul,(show K H*T = _ from (stationed F W H H' i).2),Matrix.mul_assoc]
    _ = (T.transpose*(probe S).transpose + P.transpose)*K H' := by rw [hv, smul_smul,mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_smul,add_mul]
    _ = _ := by unfold P; rw [transpose_sub,transpose_mul,add_sub_cancel]; simp
end trace
end YM.Precision
