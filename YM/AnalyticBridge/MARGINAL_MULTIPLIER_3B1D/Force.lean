import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Qualify
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical

/-!
Actual post-L mean and paired signal prices for the physical keys, jointly
with the exact identity and post-L aperture board purchases. No derivatives of
a possibly thinned source assumed for this result. Does not change the draws,
identify different sector kernels or ask for time/phase objectives.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Precision Tree Matrix
  Next.SectorChange.Schur Next.SectorChange.Wisps Next.SectorChange.Rows SectorNext.Remainder.Scales
  Next.Fluctuations FiniteMatrix Gaussian
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}

namespace SourceBounds
lemma mul_price {ι κ : Type} [Fintype ι] [Fintype κ] {H : Matrix ι κ ℝ} {a : κ → ℝ} {p : ι → Site c} {q : κ → Site c}
    {K C : ℝ} (h : Pours H p q 0 K) (hp : ∀ i, |a i| ≤ C) (hc : 0≤C) (i : ι) : |(H*ᵥa) i| ≤ K*C := by
  have he := h.row i
  simp_rw [rate,zero_mul,Real.exp_zero,one_mul] at he
  exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun j _ => (abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hp j) (abs_nonneg _)))).trans ((Finset.sum_mul ..).symm.trans_le (mul_le_mul_of_nonneg_right he hc)))

structure Signal (T : Tube G S) (x β : ℝ) (k : S.Choices) (A : Stores S) (V : Config G c) (q : Chi) (d : ℝ) (F : Forest S.ratio)
    (D E H : ℝ) : Prop where
  tilt Y i : |meanLog A F T x V k q d Y i| ≤ D
  lift Y i : |Rows.direct T x V k (shots S x) A F q d Y (meanLog A F T x V k q d Y) i| ≤ E
  buzz Y i : |Rows.eta T x V k (shots S x) A F q d Y (meanLog A F T x V k q d Y) (coupling β) i| ≤ H

variable {A : Stores S} {V : Config G c} {F : Forest S.ratio} {k : S.Choices} {q : Chi} {x β K B L η u v d : ℝ}
lemma signal_bound (Kp : kernelPrices T F x k A V η K u v) (HB : 0≤B) (_hu : 0≤u)
    (hM : Pours (Rows.move T x V k (shots S x) A F) (down S) (front A F) 0 L) (hβ : 0 < β)
    (hB : ∀ Y i, |Rows.source T x V k (shots S x) A F q d Y i| ≤ B) :
    Signal T x β k A V q d F (K*(L*B)) (L*(K*(L*B))+B) ((coupling β)⁻¹*(K*(u*rate (-v) (radiusB x/60))*(L*B))) := by
  obtain ⟨hQ,-,hL,hA,-,-,-,hE⟩ := Kp
  let W := shots S x; let Q := Rows.gram T x V k W A F; let N := per (panels A F) Q
  have hh Y i : |Rows.blame T x V k W A F q d Y i| ≤ L*B := mul_price hM.turn (hB Y) HB _
  have hlb := mul_nonneg hM.pos HB
  have hμ Y i : |meanLog A F T x V k q d Y i| ≤ K*(L*B) := by
    rw [meanLog, Matrix.neg_mulVec,Pi.neg_apply,abs_neg]; exact mul_price hL.turn (hh Y) hlb i
  refine ⟨hμ, fun Y i => (abs_add_le ..).trans (add_le_add (mul_price hM (hμ Y) (mul_nonneg hQ.pos hlb) i) (hB Y i)), fun Y i => ?_⟩
  have he : Q⁻¹.transpose = Q⁻¹ := Matrix.isHermitian_iff_isSymm.mp hA.inv.isHermitian
  have hx : N.transpose-Q⁻¹=(N-Q⁻¹).transpose := by rw [transpose_sub,he]
  have hv := hQ.fuse (hx.symm ▸ hE.turn) le_rfl
  let z := Rows.blame T x V k W A F q d Y
  change |(-(coupling β)⁻¹ • (Q *ᵥ ((-N.transpose) *ᵥ z) + z)) i| ≤ _
  rw [show Q *ᵥ ((-N.transpose) *ᵥ z) + z = -((Q*(N.transpose-Q⁻¹)) *ᵥ z) by
        rw [Matrix.neg_mulVec, mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_sub,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit),Matrix.sub_mulVec,Matrix.one_mulVec]; abel,
      Pi.smul_apply,Pi.neg_apply,smul_eq_mul, neg_mul_neg, abs_mul, abs_of_pos (inv_pos.mpr (coupling_pos hβ))]
  exact mul_le_mul_of_nonneg_left (mul_price hv (hh Y) hlb i) (inv_nonneg.mpr (coupling_pos hβ).le)



structure Power (T : Tube G S) (x β : ℝ) (k : S.Choices) (A : Stores S) (V : Config G c) (q : Chi) (d : ℝ) (F : Forest S.ratio) (E : ℝ) : Prop where
  beta : 0 < β
  paid : 1 ≤ E
  crm Y i : |meanLog A F T x V k q d Y i| ≤ E*fiery G x S.patch.L
  rows Y i : |(coupling β)⁻¹ * Rows.direct T x V k (shots S x) A F q d Y (meanLog A F T x V k q d Y) i| ≤ E*p G S.patch.L x
  fees Y i : |Rows.eta T x V k (shots S x) A F q d Y (meanLog A F T x V k q d Y) (coupling β) i| ≤ 1


end SourceBounds
open SourceBounds SectorNext.Remainder.Scales


end YM.AnalyticBridge.MarginalMultiplier3b1d
