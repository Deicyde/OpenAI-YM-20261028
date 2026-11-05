import YM.Further.GAUSSIAN_SCALAR_LEDGER.Gaussian
import YM.Next.FREE_KERNELS.Lifts
import YM.SectorNext.VACUUM_NORMALIZATION.Round


set_option warningAsError false

/-!
# Ratio matrix on regular-only or identity-completed coordinates

S below acts on the LEFT of the precision correction. Pay in
absolute row-sum (column budgets useful too but not needed here),
not assuming a symmetric AC. C must be symmetric; earn *its*
positive definiteness. The window estimates separately produce
sufficient rate inputs.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Matrix Function Filter Precision SectorNext.Vacuum
open Round (rowRate)
open scoped Topology BigOperators Matrix.Norms.Frobenius MatrixOrder

variable {ι : Type*} [Fintype ι] {A C S : Wall ι} {q : ℝ}

lemma row_entry (A : Wall ι) (h : rowRate q A) (i j : ι) : |A i j| ≤ q :=
  (Finset.single_le_sum (f := fun j => |A i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans (h i)

variable [DecidableEq ι]

lemma row_pow (S : Wall ι) (hr : rowRate q S) (hz : 0 ≤ q) (n : ℕ) : rowRate (q^n) ((-S)^n) := by
  induction n with
  | zero => intro i; simp [Matrix.one_apply, abs_ite]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact Round.ride _ _ ih (fun i => by simpa using hr i) hz

private lemma row_summable (S : Wall ι) (hr : rowRate q S) (hz : 0 ≤ q) (hq : q < 1) (i j : ι) :
    Summable fun k : ℕ => ((-S)^k) i j :=
  .of_norm_bounded (summable_geometric_of_lt_one hz hq) fun k => row_entry _ (row_pow S hr hz k) i j

private lemma sum_left (S X : Wall ι) (hr : rowRate q S) (hz : 0 ≤ q) (hq : q < 1) (i j : ι) :
    Summable fun k : ℕ => ((-S)^k * X) i j :=
  summable_sum fun b (_ : b∈Finset.univ) => (row_summable S hr hz hq i b).mul_right (X b j)

private lemma sum_right (S X : Wall ι) (hr : rowRate q S) (hz : 0 ≤ q) (hq : q < 1) (i j : ι) :
    Summable fun k : ℕ => (X * (-S)^k) i j :=
  summable_sum fun b (_ : b∈Finset.univ) => (row_summable S hr hz hq b j).mul_left (X i b)

/-- Neumann relation with termination on a true matrix; no inverse
sign assumption on S. -/
lemma build_left (X T : Wall ι) (h : (1 + S)*T = X) (hr : rowRate q S) (hz : 0 ≤ q) (hq : q < 1) (i j : ι) :
    HasSum (fun k : ℕ => ((-S)^k * X) i j) (T i j) := by
  have he (k : ℕ) : ∑ n∈Finset.range k, ((-S)^n * X) i j = T i j - ((-S)^k*T) i j := by
    simp only [← Matrix.sum_apply,← Matrix.sum_mul]
    rw [← h,← mul_assoc, show 1+S=1-(-S) by abel, geom_sum_mul_neg, Matrix.sub_mul, one_mul, Matrix.sub_apply]
  apply (sum_left S X hr hz hq i j).hasSum_iff_tendsto_nat.mpr
  simp_rw [he]; simpa using ((tendsto_const_nhds (x := T i j)).sub (sum_left S T hr hz hq i j).tendsto_atTop_zero)

lemma build_right (X T : Wall ι) (h : T*(1 + S) = X) (hr : rowRate q S) (hz : 0 ≤ q) (hq : q < 1) (i j : ι) :
    HasSum (fun k : ℕ => (X*(-S)^k) i j) (T i j) := by
  have he (k : ℕ) : ∑ n∈Finset.range k, (X * (-S)^n) i j = T i j - (T*(-S)^k) i j := by
    simp only [← Matrix.sum_apply,← Matrix.mul_sum]
    rw [← h,mul_assoc, show 1+S=1-(-S) by abel, mul_neg_geom_sum, Matrix.mul_sub, mul_one, Matrix.sub_apply]
  apply (sum_right S X hr hz hq i j).hasSum_iff_tendsto_nat.mpr
  simp_rw [he]; simpa using ((tendsto_const_nhds (x := T i j)).sub (sum_right S T hr hz hq i j).tendsto_atTop_zero)

lemma covariance_from_rate (hA : A.PosDef) (hC : C.IsHermitian) (hr : rowRate q (A*C-1))
    (hq : q < 1) : C.PosDef := by
  let G := CFC.sqrt A
  let X := G*C*G
  have hg : G*G=A := CFC.sqrt_mul_sqrt_self _ hA.posSemidef.nonneg
  have hl : Gᴴ=G := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).1
  have hn : det G ≠ 0 := by
    intro hn; have he : det A=0 := by rw [←hg,det_mul, hn,mul_zero]
    exact hA.det_pos.ne' he
  have hL := nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hn)
  have hR := mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hn)
  have hs : X.IsHermitian := by unfold X Matrix.IsHermitian; rw [conjTranspose_mul,conjTranspose_mul,hC.eq,hl,mul_assoc]
  have hh : X.PosDef := hs.posDef_iff_eigenvalues_pos.mpr fun i => by
    let v : VV ι := ⇑(hs.eigenvectorBasis i)
    let w := G*ᵥv
    let t := hs.eigenvalues i
    have hx : 0 < ‖w‖ := norm_pos_iff.mpr fun he => by
      have hv : v=0 := by rw [← one_mulVec v,←hL,←mulVec_mulVec,show G *ᵥ v=0 from he, mulVec_zero]
      exact hs.eigenvectorBasis.orthonormal.ne_zero i (by ext k; exact congr_fun hv k)
    have he : (A*C-1) *ᵥ w = (t-1) • w := by
      have hw : A*C*G= G*X := by rw [←hg]; unfold X; simp only [mul_assoc]
      rw [sub_mulVec,one_mulVec, show (A*C) *ᵥ w=(A*C*G)*ᵥ v from mulVec_mulVec .., hw,
        ← mulVec_mulVec, show X *ᵥ v=t • v from hs.mulVec_eigenvectorBasis i, mulVec_smul,sub_smul,one_smul]
    have hp := Round.rows_norm _ hr w
    rw [he,norm_smul,Real.norm_eq_abs] at hp
    have := (abs_le.mp (le_of_mul_le_mul_right hp hx)).1
    change 0 < t; linarith
  let J := G⁻¹
  have he : Jᴴ * X * J=C := by
    unfold J X; rw [conjTranspose_nonsing_inv,hl]; simp only [mul_assoc]
    rw [hR,mul_one, ←mul_assoc, hL,one_mul]
  rw [← he]
  apply hh.conjTranspose_mul_mul_same
  intro x y hx
  rw [← one_mulVec x,← hR, ← mulVec_mulVec, hx, mulVec_mulVec,hR,one_mulVec]

/-- Real symmetric precision, actual covariance—not just interpreting
its tentative log via formal series—and all three determinant prices
(including unused completions when present). Inverse series as in Echs.
`traceLog` need not use a symmetric S. -/
theorem split_costs (hA : A.PosDef) (hC : C.IsHermitian) (he : S=A*C-1) (hr : rowRate q S)
    (hz : 0 ≤ q) (hq : q < 1) :
    C.PosDef ∧ 0 < A.det ∧ 0 < C.det ∧ 0 < (1+S).det ∧
    Summable (Round.wave S) ∧ Round.traceLog S=Real.log (1+S).det ∧
    Real.log C.det= -Real.log A.det + Round.traceLog S ∧
    ∀ i j, HasSum (fun k : ℕ => ((-S)^(k+1) * A) i j) ((C⁻¹-A) i j) := by
  have h := covariance_from_rate hA hC (he ▸ hr) hq
  obtain ⟨hp,hL,hU,hT⟩ := Round.exact_trace hA hC S he hr hz hq
  have hh : 1+S=A*C := by rw [he]; abel
  refine ⟨h,hA.det_pos,h.det_pos,hL,hU,hT,?_,fun i j => ?_⟩
  · rw [hT,hh,det_mul,Real.log_mul hA.det_pos.ne' hp.ne']; abel
  have hf : (1+S)*C⁻¹=A := by rw [hh,mul_assoc,C.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hp.ne'),mul_one]
  simpa using (hasSum_nat_add_iff' 1).mpr (build_left _ _ hf hr hz hq i j)

lemma tail_ripple (S : Wall ι) (hr : rowRate q S) (hz : 0 ≤ q) (hq : q < 1) (i j : ι) (n : ℕ) :
    Summable (fun k : ℕ => Round.ripple S (k+n) i j) ∧
      ∑' k : ℕ, |Round.ripple S (k+n) i j| ≤ q ^ (n+1) / (1-q) := by
  have he (k : ℕ) : |Round.ripple S (k+n) i j| ≤ q^k * q^(n+1) := by
    unfold Round.ripple; rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < ((_ : ℕ):ℝ) +1)]
    rw [← pow_add,← Nat.add_assoc]
    exact (div_le_self (abs_nonneg _) (by push_cast; have h := Nat.cast_nonneg (α:=ℝ) k; have l := Nat.cast_nonneg (α:=ℝ) n; linarith)).trans (row_entry _ (row_pow S hr hz _) i j)
  have hl := (hasSum_geometric_of_lt_one hz hq).mul_right (q^(n+1))
  have hh := Summable.of_norm_bounded hl.summable (f := fun k : ℕ => Round.ripple S (k+n) i j) he
  refine ⟨hh, (hh.norm.tsum_le_tsum he hl.summable).trans_eq (hl.tsum_eq.trans ?_)⟩
  rw [div_eq_mul_inv,mul_comm]

end YM.Further.GaussianScalar
