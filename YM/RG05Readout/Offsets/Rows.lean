import YM.Trace.Physicalv2.Germ
import YM.Planned.PRIMARY_INTEGRAL_295.East
import YM.Push.LOCAL_SPLITTING.Comparison
/-!
# Field-weight restriction of the projection bound, using same jets
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Offsets
open Function Filter Set Lattice Labels RG Source Push.Local Wilson
open Planned.PrimaryIntegral295 WardBin
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{d:ℕ}
variable (F: Labels.Frame G d) (k:ℕ)
-- ≤k, incl scalar zero
noncomputable def basisCut : F.Coeff →ₗ[ℂ] F.Coeff where
  toFun x i := if (F.grades i).1 ≤ k then x i else 0
  map_add' x y := by ext1 i; by_cases h:(F.grades i).1 ≤ k <;> simp [h]
  map_smul' z x := by ext1 i; by_cases h:(F.grades i).1 ≤ k <;> simp [h]

lemma probity (p:Probe G d)(i:F.Index) (h:p.2.val ≠ (F.grades i).1) :
    runProbe F p (column F i)=0:=by
  rw [runProbe_eq,show F.coords.symm (column F i)=F.basis i from F.coords.injective (by rw [F.coords.apply_symm_apply,F.coords_basis];rfl)]
  let j:=p.2.val
  let ψ (t:ℝ):= read (scaleJet p.1 t) (F.basis i).val
  have hf : ψ = (fun t:ℝ=> t^(F.grades i).1 • read p.1 (F.basis i).val):= funext fun t=> scaled_grade t _ _ (F.pure i)
  have hp: leading j ψ=0:=by rw [hf,lead_monomial,if_neg h]
  have hδ: (j.factorial:ℝ)⁻¹ ≠ 0:= inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero j)
  exact smul_right_injective _ hδ (hp.trans (smul_zero _).symm)

lemma projected (p:Probe G d)(x:F.Coeff):
    runProbe F p (basisCut F k x)= if p.2.val≤k then runProbe F p x else 0:= by
  have hA(i:F.Index)(hp:p.2.val=(F.grades i).1): (if p.2.val≤k then x i else (0:ℂ)) = basisCut F k x i:=by rw [hp]; rfl
  rw [← basis_coeff (basisCut F k x),map_sum]
  split
  · next h =>
    conv_rhs => rw [← basis_coeff x,map_sum]
    refine Finset.sum_congr rfl (fun i _=>?_)
    -- NB rw replaced x inside sum on lhs?
    by_cases hr:p.2.val=(F.grades i).1
    · rw [← hA i hr,if_pos h]
    rw [map_smul,map_smul,probity F p i hr,smul_zero,smul_zero]
  next h =>
  refine Finset.sum_eq_zero (fun i _=>?_)
  by_cases hr:p.2.val=(F.grades i).1
  · rw [← hA i hr,if_neg h,zero_smul,map_zero]
  rw [map_smul,probity F p i hr,smul_zero]

lemma costs_rows (x:F.Coeff)(c:ℝ)(hc:0 ≤ c)(hp:∀ p∈ tests F, p.2.val ≤k→‖runProbe F p x‖ ≤ c):
    F.coeffSize (basisCut F k x) ≤ testPrice F*c:= by
  apply (probe_budget F).choose_spec.choose_spec.2 _ c hc
  intro p h; rw [projected]; split; next h' => exact hp p h h'
  rw [norm_zero]; exact hc
lemma cap_rows (x:F.Coeff): F.coeffSize (basisCut F k x) ≤ F.coeffSize x:=by
  apply Finset.sum_le_sum; intro i _; by_cases h:(F.grades i).1 ≤ k <;> simp [basisCut,h]
end YM.RG05Readout.Offsets
