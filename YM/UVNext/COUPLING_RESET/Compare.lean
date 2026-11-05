import YM.UVNext.COUPLING_RESET.Reset


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Quantitative conditioning even if the *activity* data are not unique

Not authorizing relabelling a Move or using differently chosen witnesses for
source computations. If two candidates are close in log-value modulo an
extensive constant on the two probes, their coupling discrepancy includes
both of their regular expenditures where the labels can actually differ.
This needs the SAME path/clip/budget data and the real unflagged probes, no
claim of intrinsic beta with arbitrarily changing paths. The result controls
in particular any difference between betas of exact lawful outputs on the
same base data, even if independently priced E / K were used there. Exact
*vacuum* comparisons always use the same normalization or pay the entire
change of partition. Size of the comparison does not grow with the torus.
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open Push.BetaTransport Lattice Wilson RG Shoot RG.Supply Input Precision Set Function Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : Side}

lemma log_flat (R : Rep G n) (h : ∀ i, R.activities.E i 1 = 0) : Real.log (R.eval 1) = R.v*sites n := by
  let A : Template G n := ⟨R.path,R.clip,R.p,fun _ _ => R.activities⟩
  have he : A.trial (fun _ => R.beta) 0 0 R.v = R := by simp [Template.trial,A]
  rw [← congr_fun (congr_arg Rep.eval he) 1,A.trial_one _ h,Real.log_exp]

lemma logs_rep (R : Rep G n) (h : ∀ i, R.activities.E i 1 = 0) {V : Config G n} (hV : flags R.p.threshold V = ∅) :
    Real.log (R.eval 1) - Real.log (R.eval V) = R.beta*kinetic R.path R.clip R.p V + R.path.inChannels R.clip R.p 0 V +
      R.activities.additive R.p V := by
  let A : Template G n := ⟨R.path,R.clip,R.p,fun _ _ => R.activities⟩
  have he : A.trial (fun _ => R.beta) 0 0 R.v = R := by simp [Template.trial,A]
  simpa only [contrast, add_zero,Template.leg,Template.background,Template.add,A] using
    (A.contrast_eq (x:=0) (d:=0) h hV (congr_fun (congr_arg Rep.eval he) 1) (H:=fun _ => R.eval) (congr_fun (congr_arg Rep.eval he) V))

variable {η κ w₁ w₂ e₁ e₂ δ₁ δ₂ : ℝ}
/-- Compare against an extensive common vacuum shift `κ*sites`. Errors per
site. No positivity on all configurations required (at tested points follows
from the represented format at those actual arguments). -/
theorem compare (R T : Rep G n) (hr : R.activities.Valid R.p δ₁ w₁) (ht : T.activities.Valid T.p δ₂ w₂)
    (hD : T.path = R.path) (hP : T.p = R.p) (hA : T.clip = R.clip)
    {V : Config G n} (hV : flags R.p.threshold V = ∅) (hη : 0 < η)
    (hp : sites n * (η*R.p.threshold^2) ≤ kinetic R.path R.clip R.p V)
    (h₀ : |Real.log (R.eval 1) - Real.log (T.eval 1) - κ * sites n| ≤ e₁ * sites n)
    (h : |Real.log (R.eval V) - Real.log (T.eval V) - κ * sites n| ≤ e₂ * sites n) :
    |R.v - T.v - κ| ≤ e₁ ∧ |R.beta - T.beta| ≤ (δ₁ + δ₂ + e₁ + e₂)/(η*R.p.threshold^2) := by
  have hv := R.p.threshold_pos
  have hpos : 0 < η*R.p.threshold^2 := by positivity
  have hk := (mul_pos (sites_pos n) hpos).trans_le hp
  have H := h₀; rw [log_flat _ hr.regular.at_flat,log_flat _ ht.regular.at_flat] at H
  constructor
  · apply le_of_mul_le_mul_right (a:=sites n) _ (sites_pos _)
    rwa [show R.v * sites n - T.v * sites n - κ * sites n = (R.v - T.v - κ) * sites n by ring,abs_mul,abs_of_pos (sites_pos n)] at H
  have h1 := logs_rep R hr.regular.at_flat hV
  have h2 := logs_rep T ht.regular.at_flat (hP.symm ▸ hV : flags T.p.threshold V = ∅)
  let k := kinetic R.path R.clip R.p V
  rw [hD,hA,hP] at h2
  have ha : |T.activities.additive R.p V| ≤ sites n * δ₂ := hP ▸ volumeE _ ht V
  have hb : |R.activities.additive R.p V| ≤ sites n * δ₁ := volumeE _ hr V
  have he : |(R.beta - T.beta)*k| ≤ (δ₁ + δ₂ + e₁ + e₂)*sites n := by
    dsimp [k]; exact abs_le.mpr ⟨by obtain ⟨ha,ha'⟩ := abs_le.mp ha; have ⟨hb,hb'⟩ := abs_le.mp hb; have ⟨hv,hv'⟩ := abs_le.mp h;
                                    obtain ⟨hu,hu'⟩ := abs_le.mp h₀; linarith,
      by have ⟨ha,ha'⟩ := abs_le.mp ha; have ⟨hb,hb'⟩ := abs_le.mp hb; have ⟨hv,hv'⟩ := abs_le.mp h;
         obtain ⟨hu,hu'⟩ := abs_le.mp h₀; linarith⟩
  apply (le_div_iff₀ hpos).mpr
  apply le_of_mul_le_mul_right (a:=sites n) _ (sites_pos _)
  rw [abs_mul,abs_of_pos hk] at he
  linarith only [mul_le_mul_of_nonneg_left hp (abs_nonneg (R.beta-T.beta)),he]


end YM.UVNext.CouplingReset
