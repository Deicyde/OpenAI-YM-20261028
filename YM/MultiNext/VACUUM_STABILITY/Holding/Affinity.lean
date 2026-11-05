import YM.MultiNext.VACUUM_STABILITY.Gaussian.Foundation

set_option warningAsError false

/-!
# Kernel score data before *literal* multipliers

Polarized advancement on the same scalar Tube, no primitive order-d derivative
estimates on the K factors. Assumes scores on the operator, a substantial
remaining physical estimate; refrains evaluating those if the unscaled multiplier would
be forced to zero by an eligibility anyway. -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Holding
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Desk Component Component.Pasture Puff Stamp
open Arrival Arrival.Flock Tune Gauss
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable (M : Theater)

/-- Background score (weaker than demanding when chart has inadmissible held
values, e.g., if using a multiplier which requires a fine seed). Earn *every*
pledged root before multiplying these multipliers, in genuine per-occurrence inventories. -/
structure Heat (useNow : M.place → Prop) (G : M.place → ℂ) (K H d u : ℝ) (p : ℕ) : Prop where
  tall : 1+(M.I:ℝ) ≤ H*(1+d)
  cooler i : adjBound (M.q i) K ∧ ∃ (w : Row (Fin M.I)) (W c b : ℝ) (S : Finset (Fin M.I)),
      (∀ i,0≤w i ∧ K*w i ≤ 1/8) ∧ ∑ i,w i ≤ W ∧ 0 ≤ c ∧ c * Real.exp (-coin K*b + 2*K*(W+S.card*coin K)) ≤ u ∧
      ∀ᵐ y ∂standard (Fin M.J), useNow (M.backTo i y) → M.roll G i y≠0 →
        let z:=mapRows (M.q i) y
        ‖M.roll G i y‖ ≤ c*(1+squares z)^p * Real.exp (pay w z) ∧ b ≤ ∑ i∈S,z i ^2

structure Priced (g : M.place → ℂ) : Prop where
  measurable i : AEStronglyMeasurable (M.roll g i) (standard (Fin M.J))
  collate : AEStronglyMeasurable (fun i => ∫ y,M.roll g i y ∂standard (Fin M.J)) M.prior

lemma respond {K H d u c : ℝ} {p : ℕ} {P : M.place → Prop} {G f g : M.place → ℂ} (h : Heat M P G K H d u p)
    (hh : ∀ i,g i=f i * G i) (hf : ∀ i,f i ≠ 0 → P i) (hc : 0 ≤ c) (hC : ∀ i, ‖f i‖ ≤ c) (hp : Priced M g) :
    M.Affords K H d (c*u) p g := by
  refine ⟨h.tall,hp.measurable,hp.collate,?_⟩
  intro i; obtain ⟨hA,w,W,C,b,S,hB,hW,hg,hU,hF⟩:=h.cooler i
  refine ⟨hA,w,W,c*C,b,S,hB,hW,mul_nonneg hc hg, (by rw [mul_assoc]; gcongr),?_⟩
  filter_upwards [hF] with y hy
  have he : M.roll g i y = f (M.backTo i y)*M.roll G i y := by unfold Theater.roll; rw [hh,Complex.real_smul,Complex.real_smul]; ring
  rw [he]; intro hb
  obtain ⟨ht,hp⟩:= hy (hf _ (left_ne_zero_of_mul hb)) (right_ne_zero_of_mul hb); refine ⟨?_,hp⟩
  rw [norm_mul,mul_assoc c,mul_assoc c]; exact mul_le_mul (hC _) ht (norm_nonneg _) hc

lemma billable (f : M.place→ℂ) (P : Priced M f) (c : ℂ) : Priced M (fun i => c*f i) := by
  have he i : M.roll (fun i => c*f i) i=fun j => c*M.roll f i j := by
    funext j; unfold Theater.roll; rw [Complex.real_smul,Complex.real_smul]; ring
  constructor
  · intro i; rw [he]; exact (P.measurable _).const_mul _
  have ht : (fun i => ∫ y,M.roll (fun i => c*f i) i y ∂standard (Fin M.J)) = fun i => c*∫ y,M.roll f i y ∂standard (Fin M.J) := by
    funext i; rw [he,integral_const_mul]
  rw [ht]; exact P.collate.const_mul _
end YM.Multi.Vacuum.Holding
