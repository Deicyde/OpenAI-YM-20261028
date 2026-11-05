import YM.Bid.Station

/-! Pairing against the predicted stationary linear tangent. -/

set_option autoImplicit false
noncomputable section

open Matrix Function
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace YM.Work.F04

open Lattice RG Wilson Precision Exterior Bid Tree Bloch

variable {G : Gauge} {c f : Side} {S : StepData c f}

lemma parts_stretch (H : Forest S.ratio) (U : Matrix (Body 1 f) (Body 1 c) ℝ)
    (x : Dir G c) (j : G.ColorIndex) :
    parts G 1 (stretch H (x, relative (S := S) H U x)) j =
      extracted S H U *ᵥ parts G 1 x j := by
  funext ⟨a, i⟩
  obtain ⟨d, rfl⟩ := axisEquiv.surjective i
  simp only [parts, stretch, axisEquiv.symm_apply_apply, PiLp.add_apply]
  by_cases hh : (a, d) ∈ H.trunks
  · have he := H.trunk_internal hh
    rw [dif_pos hh]
    change linearCopy _ _ _ j + ((0:G.Color) j) =
      (extracted S H U *ᵥ parts G 1 x j) (a, coord d)
    rw [linearCopy, if_pos he, Precision.stays H U (parts G 1 x j) (a, d) hh]
    simp
  rw [dif_neg hh]
  unfold relative
  simp

lemma parts_crop (H : Forest S.ratio) (x : Dir G c × AxisChart G H) (j : G.ColorIndex) :
    parts G 1 (crop H x) j = parts G 1 x.1 j - probe S *ᵥ parts G 1 (stretch H x) j := rfl

lemma counting_inner (x y : Dir G c) :
    ∑ i : Body 1 c, inner ℝ (x i) (y i) = ∑ j : G.ColorIndex, dotProduct (parts G 1 x j) (parts G 1 y j) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [Finset.sum_comm]
  unfold parts dotProduct
  simp only [mul_comm]

/-- In any of the tester Hessians, inserting the candidate tangent in
one slot already leaves a purely coarse pairing. Use `stationed` twice,
with *arbitrary* first slot (so this checks stationarity itself as well as
computing the quadratic value). -/
lemma test_pair (H : Forest S.ratio) (p : Clip) (W : PathData G) (B C : Bed)
    (U : Matrix (Body 1 f) (Body 1 c) ℝ) (hd : Inputs S U (B.metric.acts f) (C.metric.acts c))
    (hq : Comptroller H B p W) (z : Dir G c × AxisChart G H) (x : Dir G c) (t : S.Choices) :
    iteratedFDeriv ℝ 2 (uncurry (tested H t p W)) 0 ![z, (x, relative H U x)] =
      gaugeFiscal C z.1 x := by
  obtain ⟨hp,hk⟩ := Precision.stationed H U _ _ hd
  have he (j : G.ColorIndex) :
      parts G 1 (crop H (x, relative H U x)) j =
        S.kernel.penalty⁻¹ • (K (C.metric.acts c) *ᵥ parts G 1 x j) := by
    rw [parts_crop, parts_stretch, mulVec_mulVec, hp, sub_mulVec, one_mulVec, smul_mulVec]
    simp
  rw [(hq t).2.2, counting_inner]
  unfold gaugeFiscal
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [parts_stretch, mulVec_mulVec, hk, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    he, dotProduct_smul, smul_eq_mul, ← mul_assoc _ S.kernel.penalty⁻¹,
    mul_inv_cancel₀ S.kernel.penalty_pos.ne', one_mul, parts_crop, sub_dotProduct, add_sub_cancel]

end YM.Work.F04
