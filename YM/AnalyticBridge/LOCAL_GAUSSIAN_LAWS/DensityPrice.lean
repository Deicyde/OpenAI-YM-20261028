import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.SameQuote


/-!
# Size of density correction under the actual purchase

zeroth-order estimates; weighted sup mean shifts: accept b_i ≤ t * exp(σ d(i,o)), as
may be useful for t price also if data are at a patch anchor. Report B^-exp
cost per active link or normalized counting coordinate. For determinant keep
the active dimension and don't infer any pressure comparison. Weight s/2
loss can be paid externally. Later can specialize to local marginals with
a different dimension!
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Next SectorChange Function Set Matrix FreeResolvent
open scoped Classical BigOperators Topology

variable {ι c : Type} [Fintype ι] [DecidableEq ι] {D : Cost c} {p : ι → c}

/-- Exponential weight from a point. -/
def Meter (D : Cost c) (p : ι → c) (σ : ℝ) (o : c) (t : ℝ) (v : ι → ℝ) := ∀ i, |v i| ≤ t*D.weight σ (p i) o





namespace Meter
lemma maps {M σ t S : ℝ} {o v} {Y : Matrix ι ι ℝ} (hσ : 0 ≤ σ) (he : σ ≤ S) (ht : 0 ≤ t)
    (h : Meter D p σ o t v) (hp : D.Schur p p S M Y) : Meter D p σ o (M*t) (Y *ᵥ v) := by
  intro i
  unfold mulVec dotProduct
  calc
    |∑ x, _| ≤ ∑ x, D.weight σ (p i) (p x)*|Y i x| * (t*D.weight σ (p i) o) := by
      apply (Finset.abs_sum_le_sum_abs ..).trans
      refine Finset.sum_le_sum fun j _ => ?_; rw [abs_mul]
      have hj := D.weight_triangle hσ (p j) (p i) o
      rw [D.weight_symm σ (p j) (p i)] at hj
      calc
        _ ≤ |Y i j| *(t*(D.weight σ (p i) (p j)*D.weight σ (p i) o)) := by
          exact mul_le_mul_of_nonneg_left ((h j).trans (mul_le_mul_of_nonneg_left hj ht)) (abs_nonneg _)
        _ = _ := by ring
    _ ≤ _ := by
      rw [← Finset.sum_mul,mul_assoc M]; exact mul_le_mul_of_nonneg_right ((hp.mono he le_rfl).rows.bound i) (mul_nonneg ht (D.weight_nn ..))
end Meter

/-- ordered choice, uses b as-is. -/
def offCenter (Y : Matrix ι ι ℝ) (b : ι → ℝ) := -Y.transpose *ᵥ b

/-- If $b$ paid at σ, both means at same σ and their change at e*t.
Moreover homing error Qμ+b itself also small for either window. -/
theorem aim {Q : SectorChange.Gaussian.Table ι} {W H : ι→Set ι} {s M η C e gap : ℝ}
    (hW : Closes D p Q W s M η C e gap) (hH : Closes D p Q H s M η C e gap) {o} {σ t : ℝ} (h : 0≤σ) (he : σ≤s)
    (ht : 0≤t) {b : ι → ℝ} (hb : Meter D p σ o t b) :
    let Y := pane W Q 0; let Z := pane H Q 0
    let v := offCenter Y b; let w := offCenter Z b
    let P := Meter D p σ o
    P (C*t) v ∧ P (C*t) w ∧ P (2*e*t) (w-v) ∧
      P (M*(e*t)) (Q *ᵥ v+b) ∧ P (M*(e*t)) (Q *ᵥ w+b) := by
  intro Y Z v w P
  have hi {W : ι → Set ι} (hh : Closes D p Q W s M η C e gap) := (hh.issuer 0 le_rfl)
  simp only [add_zero,inv_one,mul_one,one_pow] at hi
  have ha {Y : Matrix ι ι ℝ} {M : ℝ} (hm : D.Schur p p s M Y) : P (M*t) (offCenter Y b) := hb.maps h he ht (hm.transpose.neg)
  have hx := switchPrice hW hH |>.1
  have hq : Q.IsSymm := Matrix.isHermitian_iff_isSymm.mp hW.primal.isHermitian
  have hl : (resolve Q 0).transpose=Q⁻¹ := by rw [(symm_resolve Q hq 0).eq]; unfold resolve; simp
  have H' {Y : Matrix ι ι ℝ} (hv : D.Schur p p s e (Y-resolve Q 0)) : P (M*(e*t)) (Q *ᵥ offCenter Y b+b) := by
    have hf := ha hv
    -- no place for e nonneg? derive or price if t*M or empty
    by_cases h₀ : IsEmpty ι
    · intro i; exact isEmptyElim i
    haveI := not_isEmpty_iff.mp h₀
    have hN : 0 ≤ e := by
      let i : ι := Classical.arbitrary _
      exact (Finset.sum_nonneg (s:=Finset.univ) (fun j _ => mul_nonneg (D.weight_nn s (p i) (p j)) (abs_nonneg ((Y-resolve Q 0) i j)))).trans (hv.rows.bound _)
    have hh : Q *ᵥ offCenter Y b+b=Q *ᵥ offCenter (Y-resolve Q 0) b := by
      unfold offCenter; rw [transpose_sub,hl,neg_sub,sub_eq_add_neg,add_comm Q⁻¹,Matrix.add_mulVec,Matrix.mulVec_add,Matrix.mulVec_mulVec b Q Q⁻¹,
        Q.mul_nonsing_inv (Q.isUnit_iff_isUnit_det.mp hW.primal.isUnit),Matrix.one_mulVec]
    rw [hh]; exact hf.maps h he (mul_nonneg hN ht) hW.pays
  refine ⟨ha (hi hW).1,ha (hi hH).1,?_,H' (hi hW).2.2.2,H' (hi hH).2.2.2⟩
  have hm := ha (Y:=Y-Z) hx
  unfold w v offCenter
  rw [← Matrix.sub_mulVec]
  have ht : D.Schur p p s (2*e) (-Z.transpose- -Y.transpose) := by
    rw [show -Z.transpose- -Y.transpose=(Y-Z).transpose from (by rw [transpose_sub]; abel)]
    exact hx.transpose
  exact hb.maps h he ‹0≤t› ht

namespace Density
open SectorChange.Gaussian


-- variant includes determinant

end Density
end YM.AnalyticBridge.LocalGaussianLaws
