import YM.Next.WARD_BIN.Flags

/-!
# Extraction to kernel projectors on the actual shelves

Keeps columns
on (sup) native norms; only constructs projections via aux Hilbert space.

Supplied analysis upstream can retain THIS extraction and S.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter Wilson RG Source Extraction Extraction.Lease Bid MeasureTheory Dash
open scoped BigOperators Topology Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {d : ℕ} {A : Chart C d} (Z : Shelf A)




section Hilbert
variable {V X : Type*} [NormedAddCommGroup V] [NormedAddCommGroup X] [NormedSpace ℂ V]
  [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
variable (Q : V ≃L[ℂ] X)

def sideStar (E : Submodule ℂ V) : V →L[ℂ] V := ContinuousLinearMap.id _ _ - Q.symm.toContinuousLinearMap ∘L
    ((E.map (Q.toLinearEquiv : V→ₗ[ℂ] X)).starProjection ∘L Q.toContinuousLinearMap)
lemma streak (E : Submodule ℂ V) (p) : sideStar Q E p=p-Q.symm ((E.map (Q.toLinearEquiv : V→ₗ[ℂ] X)).starProjection (Q p)) := rfl
lemma side_star (E : Submodule ℂ V) (p) : sideStar Q E p=0 ↔ p∈E := by
  rw [streak,sub_eq_zero,← Q.injective.eq_iff, Q.apply_symm_apply, eq_comm, Submodule.starProjection_eq_self_iff]; constructor
  · rintro ⟨v,hv,H⟩; exact Q.injective H ▸ hv
  intro h; exact ⟨_,h,rfl⟩
lemma side_idem (E : Submodule ℂ V) (p) : sideStar Q E (sideStar Q E p)=sideStar Q E p := by
  nth_rw 2 [streak]
  let q := (E.map (Q.toLinearEquiv : V→ₗ[ℂ] X)).starProjection (Q p)
  obtain ⟨v,hv,(H : Q v=q)⟩ := Submodule.starProjection_apply_mem (E.map (Q.toLinearEquiv : V→ₗ[ℂ] X)) (Q p)
  change sideStar _ _ (_-Q.symm q)=_
  rw [← H,Q.symm_apply_apply,map_sub,(side_star Q E v).mpr hv, sub_zero]
lemma edge_price : ∃ A : ℝ, ∀ E : Submodule ℂ V, ‖sideStar Q E‖ ≤ A := by
  refine ⟨‖ContinuousLinearMap.id ℂ V‖+ ‖Q.symm.toContinuousLinearMap‖ * (1*‖Q.toContinuousLinearMap‖),fun E => ?_⟩
  refine (norm_sub_le ..).trans (add_le_add le_rfl ((ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul_of_nonneg_left
    ((ContinuousLinearMap.opNorm_comp_le ..).trans ?_) (norm_nonneg _))))
  exact mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le _) (norm_nonneg _)


end Hilbert

namespace Shelf
def spar (i : Pair) := sideStar (PiLp.continuousLinearEquiv 2 ℂ (fun _ : (brim C d).Index => ℂ)).symm
  (LinearMap.range (Z.panel i))
lemma step_power (i) (v) : Z.spar i (Z.spar i v)=Z.spar i v := side_idem ..
lemma spans_out (i) : LinearMap.ker (Z.spar i).toLinearMap = LinearMap.range (Z.panel i) :=
  Submodule.ext fun x => side_star _ _ x
lemma bounded : ∃ B : ℝ, ∀ i, ‖Z.spar i‖ ≤ B := by
  obtain ⟨R,H⟩:= edge_price (PiLp.continuousLinearEquiv 2 ℂ (fun _ : (brim C d).Index => ℂ)).symm
  exact ⟨R,fun i => H (LinearMap.range (Z.panel i))⟩

end Shelf

-- Compact diagonal twice; never selecting based on a spectator.




end YM.WardBin
