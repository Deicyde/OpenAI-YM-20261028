import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Orbit
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Stone

/-!
# The signed calibration boards at controlled price. Only on actual room.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.Statue
open Filter Function Set Lattice Wilson Labels RG Cells Source Source.Drops WilsonStartup
open Work Push.Corrected Push.Uniform Push.CutoffProjectors Collapse PathCost Building Growth Fund Next.Foundations
open Stone ProjectorNext.Equivariance
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side} {m p l W : ℕ} {C : Family G} {h : distant n m}

private lemma line_budget {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {l : ℕ} {c r : ℝ} (he : f 0=0) (hr : Allows l f 0 c)
    (hg : 0<r) (hl : r ≤ 1) : Allows l (fun t => r⁻¹ • f (r • t)) 0 c := by
  let L := r • ContinuousLinearMap.id ℝ E
  have hm : Allows l f (L 0) c := by rw [L.map_zero]; exact hr
  have hp : ContDiffAt ℝ ω (f ∘ L) 0 := hm.analytic.comp 0 L.contDiff.contDiffAt
  refine ⟨hp.const_smul r⁻¹,fun i hi => ?_⟩
  cases i with
  | zero => rw [norm_iteratedFDeriv_zero]; simp [he,hr.nonneg]
  | succ i =>
    change ‖iteratedFDeriv ℝ (i+1) (r⁻¹ • (f ∘ L)) 0‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply (hp.of_le le_top),jets_linear _ (hr.analytic.of_le le_top),norm_smul,Real.norm_of_nonneg (inv_pos.mpr hg).le]
    apply (mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) (inv_pos.mpr hg).le).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hv : ‖L‖ ≤ r := ContinuousLinearMap.opNorm_le_bound _ hg.le fun v => by
      change ‖r • v‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg hg.le]
    have hz : ‖L‖^(i+1) ≤ r := by rw [pow_succ]; exact (mul_le_of_le_one_left (norm_nonneg L) (pow_le_one₀ (norm_nonneg L) (hv.trans hl))).trans hv
    apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (hr.norm_le _ hi) hz (pow_nonneg (norm_nonneg _) _) hr.nonneg) (inv_pos.mpr hg).le)
    rw [mul_comm c r,inv_mul_cancel_left₀ hg.ne']

theorem relative (G : Gauge) (l : ℕ) : ∃ b : Fund, ∀ R : ℝ, 1 ≤ R → ∀ n m, ∀ h : distant n m, ∀ P : BudgetPoint,
    (wall m:ℝ)^2 ≤ R → Allows l (see G l h P).replay 0 (b.rents R) := by
  obtain ⟨a,ha⟩ := account G l; exact ⟨a,fun R u n m h P e =>
    line_budget (cleared G h) (ha R u n m h e) P.threshold_pos P.threshold_le⟩
private lemma tracked (s : Signed) {P : BudgetPoint} (B : Board G n P l) : ‖Compass.retract B s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro v; rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 ; intro i
  have hw := Compass.wind_sq s (B.leg i).plaq
 -- explicit term
  change ‖Compass.wind s (B.leg i).plaq • v i‖ ≤ _
  have he : Compass.wind s (B.leg i).plaq=1 ∨ Compass.wind s (B.leg i).plaq= -1 := by
    apply eq_or_eq_neg_of_sq_eq_sq; rw [pow_two,hw,one_pow]
  rw [norm_smul,show ‖Compass.wind s (B.leg i).plaq‖=1 from he.elim (fun e => by rw [e]; simp) (fun e => by rw [e]; simp),one_mul]
  exact norm_le_pi_norm ..
private lemma invest (s : Signed) : ‖(Compass.invert s : Directions G n →L[ℝ] Directions G n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro v; rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 ; intro i
  change ‖roll _ _ _ _ _‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]; exact norm_le_pi_norm ..

variable (G) in
theorem turnRate (l : ℕ) : ∃ b : Fund, ∀ R : ℝ, 1 ≤ R → ∀ n m, ∀ h : distant n m, ∀ P : BudgetPoint,
    (wall m:ℝ)^2 ≤ R → let B:=see G l h P; ∀ (s : Signed) (ht : Compass.vacancy B s),
      Allows l (Compass.arrow B s ht).replay 0 (b.rents R) := by
  obtain ⟨a,ha⟩ := relative G l
  obtain ⟨b,hb⟩ := combines l a (flat 1)
  refine ⟨b,fun R u n m h P H => ?_⟩
  intro B s ht
  rw [← one_mul (b.rents R)]
  change Allows l ((Compass.invert s : Directions G n →L[ℝ] Directions G n) ∘ (B.replay ∘ Compass.retract B s)) (0:B.Eye) _
  refine Allows.linear (Compass.invert s) (f:=B.replay ∘ Compass.retract B s) ?_ (invest s)
  refine Allows.mono (Allows.comp (g:=B.replay) (f:=Compass.retract B s) ?_ ?_) (hb R u)
  · rw [map_zero]; exact ha R u n m h P H
  exact allows_linear ((tracked s B).trans (cash _ _)) (by rw [map_zero,norm_zero]; exact (gain _ u).le)





lemma slides (G : Gauge) (h : distant n m) (P : BudgetPoint) (l : ℕ) (s : Signed) :
    Compass.vacancy (see G l h P) s := by
  intro i; refine vacancy_at h (Compass.bend G s (path G h i)) ?_
  have hu := Compass.lesser G s (path G h i)
  change (Compass.bend G s (path G h i)).walk.length + 4 ≤ limitsight m
  have hx : (path G h i).walk.length ≤ wall m := dated ..
  unfold limitsight; omega

-- true movement on this chart







end YM.Further.CorrectedLift.Statue
