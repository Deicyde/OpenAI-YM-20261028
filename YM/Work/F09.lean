import YM.Bid.Craft

/-!
# The real, period-by-period algebra of the stack

From `Replaces`, the matrix identities in `Floor`, the two transport identities in
`Diagonal` and the given factorization of the defect. In particular the Gram on the
whole source of the stack (incl. harmonics); no spectral estimates are used or asserted.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Work.F09
open Lattice RG Precision Craft Bloch Exterior

private lemma symmetric_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W R : Matrix ι ι ℝ) (h : W * R = 1) (hW : W.transpose = W) : R.transpose = R := by
  have ht : R.transpose * W = 1 := by
    rw [← hW, ← Matrix.transpose_mul, h, Matrix.transpose_one]
  calc
    R.transpose = R.transpose * (W * R) := by rw [h, Matrix.mul_one]
    _ = R := by rw [← Matrix.mul_assoc, ht, Matrix.one_mul]

private lemma stack_gram {n : Side} {α β θ : Type*} [Fintype α] [Fintype β]
    (U : Matrix (Co n α) θ ℝ) (V : Matrix (Co n β) θ ℝ) :
    (stack U V).transpose * stack U V = U.transpose * U + V.transpose * V := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Finset.sum_add_distrib, Matrix.transpose_apply, stack,
    Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]

private lemma stack_mul {n : Side} {α β θ φ : Type*} [Fintype θ]
    (U : Matrix (Co n α) θ ℝ) (V : Matrix (Co n β) θ ℝ) (Y : Matrix θ φ ℝ) :
    stack U V * Y = stack (U * Y) (V * Y) := by
  ext ⟨x, a|b⟩ j <;> rfl

private lemma stack_zero {n : Side} {α β θ : Type*} :
    stack (0 : Matrix (Co n α) θ ℝ) (0 : Matrix (Co n β) θ ℝ) = 0 := by
  ext ⟨x, a|b⟩ j <;> rfl

theorem answer : YM.Bid.F09 := by
  intro c f S A B H H' P C p q x y v w replacement fine coarse diagonal factor bleep

  let s := Real.sqrt S.kernel.penalty
  have hs : s ≠ 0 := (Real.sqrt_pos.2 S.kernel.penalty_pos).ne'
  have hss : s⁻¹ * s⁻¹ = S.kernel.penalty⁻¹ := by
    rw [← mul_inv_rev, show s * s = _ from Real.mul_self_sqrt S.kernel.penalty_pos.le]

  let J := H.full p f
  let J' := H'.full q c
  let W := H.metric.acts f
  let W' := H'.metric.acts c
  let R := H.inverse.acts f
  let R' := H'.inverse.acts c
  let D := Exterior.d 1 f
  let D' := Exterior.d 1 c
  let E := Exterior.d 2 c
  let T := installed S.ratio A.T

  have hJ : J.transpose * J = W := fine.roots
  have hJ' : J'.transpose * J' = W' := coarse.roots
  have hRs : R.transpose = R := symmetric_inverse W R fine.inverse fine.symmetric.1
  have hRs' : R'.transpose = R' := symmetric_inverse W' R' coarse.inverse coarse.symmetric.1
  have hR : R * W = 1 := mul_eq_one_comm.mp fine.inverse
  have hR' : R' * W' = 1 := mul_eq_one_comm.mp coarse.inverse
  have hW' : W' * R' = 1 := coarse.inverse
  have hTJ : T * W' * D' = W * D * installed S.ratio A.A0 := by
    have hc : W' * D' = H'.diagonal.acts c * D' := coarse.same
    have hf : W * D = H.diagonal.acts f * D := fine.same
    rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, hf]
    exact diagonal.stays

  -- The coarse projector Q and the additional row X for its complement calculation
  let Q := J' * R' * J'.transpose
  let X := P.acts c * E * R' * J'.transpose
  have hQJ : Q * J' = J' := calc
    Q * J' = J' * (R' * (J'.transpose * J')) := by simp only [Q, Matrix.mul_assoc]
    _ = J' := by rw [hJ', hR', Matrix.mul_one]
  have hQs : Q.transpose = Q := by
    simp only [Q, Matrix.transpose_mul, Matrix.transpose_transpose, hRs', Matrix.mul_assoc]
  have hQ : Q * Q = Q := calc
    Q * Q = Q * J' * R' * J'.transpose := by simp only [Q, Matrix.mul_assoc]
    _ = Q := by rw [hQJ]

  have hM : installed S.ratio B.mf = J * R * T * J'.transpose := replacement.mf
  have hm : B.mn.acts c = s⁻¹ • (D'.transpose * J'.transpose) := replacement.mn
  have hN : B.o.acts c = stack (1-Q) X := replacement.image
  have hmt : (B.mn.acts c).transpose = s⁻¹ • (J' * D') := by
    rw [hm, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose]

  constructor
  · let Z := R' - T.transpose * R * T - S.kernel.penalty⁻¹ • (D' * D'.transpose)
    have hz : W' * Z * W' = E.transpose * C.acts c * E := bleep
    have gramX : X.transpose * X = J' * Z * J'.transpose := calc
      X.transpose * X = J' * R' *
          (E.transpose * ((P.acts c).transpose * P.acts c) * E) * R' * J'.transpose := by
        simp only [X, Matrix.transpose_mul, Matrix.transpose_transpose, hRs', Matrix.mul_assoc]
      _ = J' * R' * (W' * Z * W') * R' * J'.transpose := by rw [← factor c, ← hz]
      _ = J' * (R' * W') * Z * (W' * R') * J'.transpose := by simp only [Matrix.mul_assoc]
      _ = J' * Z * J'.transpose := by rw [hR', hW', Matrix.mul_one, Matrix.mul_one]
    have gramN : (B.o.acts c).transpose * B.o.acts c = (1-Q) + J'*Z*J'.transpose := by
      have he : (1-Q).transpose * (1-Q) = 1-Q := by
        rw [Matrix.transpose_sub, Matrix.transpose_one, hQs, Matrix.sub_mul,
          Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hQ, sub_self, sub_zero]
      rw [hN, stack_gram, gramX, he]
    have gramF : (installed S.ratio B.mf).transpose * installed S.ratio B.mf =
        J' * (T.transpose * R * T) * J'.transpose := calc
      _ = J' * (T.transpose * (R * (J.transpose * J)) * R * T) * J'.transpose := by
        simp only [hM, Matrix.transpose_mul, Matrix.transpose_transpose, hRs, Matrix.mul_assoc]
      _ = _ := by rw [hJ, hR, Matrix.mul_one]
    have gramC : (B.mn.acts c).transpose * B.mn.acts c =
        J' * (S.kernel.penalty⁻¹ • (D' * D'.transpose)) * J'.transpose := by
      rw [hmt, hm]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, Matrix.mul_assoc]
    rw [gramF, gramC, gramN]
    dsimp only [Q, Z]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  · change s • _ = _
    rw [hmt, smul_smul, mul_inv_cancel₀ hs, one_smul]
  · change installed S.ratio B.mf * J' * D' = J * D * _
    rw [hM, ← replacement.first]
    calc
      J * R * T * J'.transpose * J' * D' = J * R *
          (T * (J'.transpose * J') * D') := by simp only [Matrix.mul_assoc]
      _ = J * R * (W * D * installed S.ratio A.A0) := by rw [hJ', hTJ]
      _ = J * (R * W) * D * installed S.ratio A.A0 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR, Matrix.mul_one]
  · change B.mn.acts c * J' * D' = s⁻¹ • (D'.transpose * W' * D')
    rw [hm, ← hJ']
    simp only [Matrix.smul_mul, Matrix.mul_assoc]
  · change B.o.acts c * J' * D' = 0
    have hh : (1-Q) * J' = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hQJ, sub_self]
    have he : X * J' * D' = 0 := calc
      X * J' * D' = P.acts c * E * (R' * (J'.transpose * J')) * D' := by
        simp only [X, Matrix.mul_assoc]
      _ = P.acts c * (E * D') := by rw [hJ', hR', Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by rw [show E * D' = 0 from Exterior.closed 1 c, Matrix.mul_zero]
    rw [hN, stack_mul, stack_mul, he, hh, Matrix.zero_mul, stack_zero]
  change (installed S.ratio B.mf).transpose * (J * D) +
    (B.mn.acts c).transpose * (- s • mean S) = 0
  have hf : (installed S.ratio B.mf).transpose * (J * D) = J' * D' * mean S := calc
    _ = J' * T.transpose * (R * (J.transpose * J)) * D := by
      simp only [hM, Matrix.transpose_mul, Matrix.transpose_transpose, hRs, Matrix.mul_assoc]
    _ = J' * (T.transpose * D) := by rw [hJ, hR, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [show T.transpose * D = _ from diagonal.transport, Matrix.mul_assoc]
  rw [hf, hmt]
  simp only [neg_smul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ hs, one_smul, add_neg_cancel]

end YM.Work.F09
