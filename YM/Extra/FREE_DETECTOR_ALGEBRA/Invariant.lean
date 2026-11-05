import YM.Extra.FREE_DETECTOR_ALGEBRA.Filtrate
import YM.Extra.FREE_DETECTOR_ALGEBRA.Pages
import YM.Extra.FREE_DETECTOR_ALGEBRA.PowerGram

set_option warningAsError false

/-!
# Projection on bounded fields and invariant preimages

Compact-color argument via the positive point detector, no abstract compact
extension. Real form on polynomial modules even when spanning the ideal over
complex coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {G : Gauge} {j k n : ℕ}

def folio (G : Gauge) (l k : ℕ) := pages G l ⊓ MvPolynomial.weightedHomogeneousSubmodule ℂ letterCount k

lemma folio_order : folio G j k ≤ through G ((j+2) * k) := by
  classical
  intro p hp
  have hs := (inBook p j).mp hp.1
  refine (MvPolynomial.mem_restrictSupport_iff ℂ).mpr fun i hi => ?_
  have he := hp.2 (MvPolynomial.mem_support_iff.mp (show i ∈ p.support from hi))
  change Finsupp.weight costKey i ≤ _
  rw [← he,Finsupp.weight_apply,Finsupp.weight_apply]; unfold Finsupp.sum; rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv; have ht := hs v ((MvPolynomial.mem_vars_iff_mem_support v).mpr ⟨i,hi,hv⟩)
  change i v * (v.1+2) ≤ _
  rw [show (j+2)*(i v • letterCount v)=i v*(j+2) by simp [letterCount,mul_comm]]
  exact Nat.mul_le_mul_left _ (by omega)

instance through_small (j : ℕ) : FiniteDimensional ℂ (through G j) := by
  let f : through G j →ₗ[ℂ] limited G j := (writeRaw.toLinearMap.comp ((through G j).subtype)).codRestrict _ fun p =>
    filterMove costKey generation writeRaw (gradientWrite (·+2)) (show p.val∈byWeight costKey _ from p.property)
  refine FiniteDimensional.of_injective f fun p q he => ?_
  have hv : writeRaw p.val = writeRaw q.val := congr_arg Subtype.val he
  apply Subtype.ext; rw [← writeRaw_after p.val,hv,writeRaw_after]

instance folio_bound (j k : ℕ) : FiniteDimensional ℂ (folio G j k) := by
  have ht : Injective (Submodule.inclusion (folio_order (G:=G) (k:=k) (j:=j))) := Submodule.inclusion_injective _
  exact FiniteDimensional.of_injective _ ht

/-- Orthogonal action on space of these polys. -/
def ink (G : Gauge) : WickPol G →ₗ[ℝ] WickPol G →ₗ[ℝ] ℝ where
  toFun p :=
    { toFun q := (duplex 0 (basis 0) p q).re
      map_add' q r := by unfold duplex; rw [_root_.map_add,_root_.map_add,Complex.add_re]
      map_smul' t q := by
        have he : t • q = (t:ℂ) • q := (IsScalarTower.algebraMap_smul ℂ t q).symm
        unfold duplex; rw [he,bar_scaled,_root_.map_smul]; simp [smul_eq_mul] }
  map_add' p q := by ext r; simp [duplex]
  map_smul' t p := by
    apply LinearMap.ext; intro r
    have he : t • p = (t:ℂ) • p := (IsScalarTower.algebraMap_smul ℂ t p).symm
    change (duplex _ _ (t • p) r).re=t*(duplex _ _ p r).re
    unfold duplex; rw [he,_root_.map_smul,LinearMap.smul_apply]; simp









section lift
variable {A U V : Type*} [Group A] [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U] [AddCommGroup V] [Module ℝ V]


end lift
end YM.Extra.FD
