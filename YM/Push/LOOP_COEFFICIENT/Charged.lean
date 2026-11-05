import YM.Push.LOOP_COEFFICIENT.DriftOperators
import YM.Push.LOOP_COEFFICIENT.MeshMean
import YM.Push.LOOP_COEFFICIENT.Vertex

/-!
# Rooted gradient trace and double contraction on a periodic mesh

`one` slot belongs to the charge test (-p in an opposite pairing with
an external background field); `two` is charge test / derivative in the
background, in this order. It has NO required permutation symmetry. The
`Vertex.base` field in a `Charged` hypothesis is immaterial.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Filter Set Bloch Laurent Lattice
open scoped Topology BigOperators ContDiff
variable {n : Side} {m k a d : Type} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k] [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a]

section position
open scoped Matrix.Norms.Frobenius RealTrace

def charge₁ (R : (m → ℝ) → RealTrace m k) := color₁ (fun v => cmat (R 0 v))
def charge₂ (R : (m → ℝ) → RealTrace m k) := color₂ (fun v w => cmat (fderiv ℝ R 0 w v))
lemma charge₁_value (R : (m → ℝ) → RealTrace m k) (x : m → ℝ) : charge₁ R (cvec x) = cmat (R 0 x) := color₁_real (cmat.comp (R 0).toLinearMap) x
lemma charge₂_value (R : (m → ℝ) → RealTrace m k) (x y : m → ℝ) : charge₂ R (cvec x) (cvec y) = cmat (fderiv ℝ R 0 y x) := color₂_real ((fderiv ℝ R 0).toLinearMap₁₂.flip.compr₂ cmat) x y

lemma charge₁_pair (R : (m → ℝ) → RealTrace m k) (x y : CSpace m) : x ⬝ᵥ (cmat (accCoeff R) *ᵥ y) = (charge₁ R x * charge₁ R y).trace := by
  let T := ((matrixMulLinear k k k ℂ).compl₁₂ (charge₁ R) (charge₁ R)).compr₂ (traceLinearMap k ℂ ℂ)
  rw [← Matrix.toLinearMap₂'_apply',show Matrix.toLinearMap₂' ℂ (cmat (accCoeff R)) = T from complex_ext₂ fun v w => ?_]; rfl
  change _ = (charge₁ R (cvec v) * charge₁ R (cvec w)).trace
  rw [Matrix.toLinearMap₂'_apply',cmat_mulVec,cvec_dot,double_pair,charge₁_value,charge₁_value,← cmat_mul,cmat_trace]
lemma charge₂_pair (R : (m → ℝ) → RealTrace m k) (x y : CSpace m) : x ⬝ᵥ (cmat (respCoeff R) *ᵥ y) = (charge₂ R x y).trace := by
  rw [← Matrix.toLinearMap₂'_apply', show Matrix.toLinearMap₂' ℂ (cmat (respCoeff R)) = _ from (complex_ext₂ (T:=(charge₂ R).compr₂ (traceLinearMap k ℂ ℂ)) fun v w => ?_)]; rfl
  change _ = (charge₂ R (cvec v) (cvec w)).trace
  rw [Matrix.toLinearMap₂'_apply',cmat_mulVec,cvec_dot,response_pair,charge₂_value,cmat_trace]

structure Charged (A : Grid n m a) (B : Grid n k d) (R : (m → ℝ) → RealTrace m k) (V : Vertex a d d) : Prop where
  one {q p k i} : Matches q k → Matches p i → ∀ v, Routed B B (k+i) k (charge₁ R (plane A i *ᵥ v)) (V.one q p v)
  two {q p s k i j} : Matches q k → Matches p i → Matches s j → ∀ v w, Routed B B (k+i+j) k (charge₂ R (plane A i *ᵥ v) (plane A j *ᵥ w)) (V.two q p s v w)
end position

def reverseTrace (V : Vertex a d d) (x y : CSpace a) (p q : Momentum) := (V.one (q+p) (-p) x * V.one q p y).trace

def respTrace (V : Vertex a d d) (x y : CSpace a) (p q : Momentum) := (V.two q (-p) p x y).trace

def kernelOf (f : CSpace a → CSpace a → Momentum → Momentum → ℂ) (p : Momentum) := of fun i j => boxMean (f (Pi.single i 1) (Pi.single j 1) p)

variable {V U : Vertex a d d}
variable {A : Grid n m a} {B : Grid n k d}

section sampled
open scoped Matrix.Norms.Frobenius RealTrace
variable {R : (m → ℝ) → RealTrace m k} {X : (m → ℝ) → Matrix k k ℝ} (h : Charged A B R U)

def Vertex.amplify (V U : Vertex a d d) : Vertex a d d where
  base _ := 0
  one q p := ((matrixMulLinear d d d ℂ) (V.base (q+p))).comp (U.one q p)
  two q p s := (U.two q p s).compr₂ ((matrixMulLinear d d d ℂ) (V.base (q+p+s))) + ((matrixMulLinear d d d ℂ).compl₁₂ (V.one (q+p) s) (U.one q p)).flip

lemma charge₁_amp (v) : charge₁ (amplify X R) v = (actualMatrix X).base * charge₁ R v := by
  rw [show charge₁ (amplify X R) = _ from complex_ext (T:=((matrixMulLinear k k k ℂ) (actualMatrix X).base).comp (charge₁ R)) (fun v => ?_)]; rfl
  change charge₁ (amplify X R) _ = cmat (X 0) * charge₁ R _; rw [charge₁_value,charge₁_value,← cmat_mul]; rfl

lemma charge₂_amp (hx : ContDiffAt ℝ ω X 0) (hr : ContDiffAt ℝ ω R 0) (v w) : charge₂ (amplify X R) v w = (actualMatrix X).base * charge₂ R v w +
    (actualMatrix X).lin w * charge₁ R v := by
  rw [show charge₂ (amplify X R) = _ from complex_ext₂ (T:=(charge₂ R).compr₂ ((matrixMulLinear k k k ℂ) (actualMatrix X).base) + ((matrixMulLinear k k k ℂ).compl₁₂ (actualMatrix X).lin (charge₁ R)).flip) fun v w => ?_]; rfl
  change charge₂ (amplify X R) _ _ = cmat (X 0) * charge₂ R _ _ + (actualMatrix X).lin _ * charge₁ R _
  rw [charge₂_value,charge₂_value,charge₁_value,actualMatrix, actual_real₁,← cmat_mul,← cmat_mul,← map_add]; congr 1
  have he := hr.differentiableAt (by simp); have hh := hx.differentiableAt (by simp)
  let a := amplify X R
  have hA := (amplify_diff hx hr).differentiableAt (by simp)
  have ht : fderiv ℝ a 0 w v = fderiv ℝ (fun b => X b * R b v) 0 w := by rw [show fderiv ℝ (fun b => X b * R b v) 0 = _ from (hA.hasFDerivAt.clm_apply (hasFDerivAt_const v _)).fderiv]; simp [a]; rfl
  rw [ht,show fderiv ℝ (fun b => X b * R b v) 0 = _ from ((matrixMulCLM k k k).hasFDerivAt_of_bilinear hh.hasFDerivAt (he.hasFDerivAt.clm_apply (hasFDerivAt_const v _))).fderiv]; simp only [ContinuousLinearMap.comp_zero,zero_add]; rfl

include h
lemma Charged.amplify (hx : ContDiffAt ℝ ω X 0) (hr : ContDiffAt ℝ ω R 0) (he : Synced A B B (actualMatrix X) V) : Charged A B (amplify X R) (V.amplify U) := by
  constructor
  · intro q p k i hq hp v; rw [charge₁_amp]; exact (he.base (hq.add hp)).mul (h.one hq hp v)
  intro q p s k i j hq hp hs v w; rw [charge₂_amp hx hr]; exact ((he.base (hq.add hp |>.add hs)).mul (h.two hq hp hs v w)).add ((he.one (hq.add hp) hs w).mul (h.one hq hp v))

omit h [DecidableEq m] in
lemma sample_dot (X : Matrix m m ℂ) (i j : Site n) (u v : a) : sample A A X i j u v = ((n.val:ℂ)^4)⁻¹ *
    ((plane A i *ᵥ Pi.single u 1) ⬝ᵥ (X *ᵥ plane A j *ᵥ Pi.single v 1)) := by
  rw [← vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]; simp [sample,Matrix.mul_assoc]

private lemma trace₁ {p s : Momentum} {i j : Site n} (hi : Matches s i) (hj : Matches p j) (x y : CSpace a) :
    (charge₁ R (plane A i *ᵥ x) * charge₁ R (plane A j *ᵥ y)).trace =
      if i+j = 0 then ∑ k : Site n,(U.one (mon k + p) s x * U.one (mon k) p y).trace else 0 := by
  rw [add_comm i j]
  exact Routed.trace fun k => add_assoc k j i ▸ (h.one ((mon_matches k).add hj) hi x).mul (h.one (mon_matches k) hj y)
private lemma trace₂ {p s : Momentum} {i j : Site n} (hi : Matches s i) (hj : Matches p j) (x y : CSpace a) :
    (charge₂ R (plane A i *ᵥ x) (plane A j *ᵥ y)).trace =
      if i+j = 0 then ∑ k : Site n,(U.two (mon k) s p x y).trace else 0 :=
  Routed.trace fun k => add_assoc k i j ▸ h.two (mon_matches k) hi hj x y

lemma charge₁_sample (i j : Site n) {p : Momentum} (hp : Matches p j) (x y : a) :
    sample A A (cmat (accCoeff R)) i j x y = if i+j = 0 then meshMean n (reverseTrace U (Pi.single x 1) (Pi.single y 1) p) else 0 := by
  rw [sample_dot,charge₁_pair]; split
  next he => rw [eq_neg_of_add_eq_zero_left he,trace₁ h hp.neg hp,if_pos (neg_add_cancel j)]; rfl
  next he => rw [trace₁ h (mon_matches i) hp, if_neg he,mul_zero]
lemma charge₂_sample (i j : Site n) {p : Momentum} (hp : Matches p j) (x y : a) :
    sample A A (cmat (respCoeff R)) i j x y = if i+j = 0 then meshMean n (respTrace U (Pi.single x 1) (Pi.single y 1) p) else 0 := by
  rw [sample_dot,charge₂_pair]; split
  next he => rw [eq_neg_of_add_eq_zero_left he,trace₂ h hp.neg hp,if_pos (neg_add_cancel j)]; rfl
  next he => rw [trace₂ h (mon_matches i) hp, if_neg he,mul_zero]
end sampled
end YM.Push.Loops
