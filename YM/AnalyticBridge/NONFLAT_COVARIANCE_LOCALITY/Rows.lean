import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Reads
import YM.Push.FREE_RESOLVENT.Polar
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gap


/-!
# Affine table on the real branch

Feed the actual D and its derivatives to FR. Denote parent distances at
active/tensor slots by `front` and `down` as in GaussianSectorChange. Both
a link and its Co-parent may occur many times; keep even all repeated
position weights. Counting mass receipt post-L. Does not provide pre-L
prices here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Function Filter Lattice RG Pressure Precision Wilson Tree 
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows
  
open Push.SectorMeasure
open FreeResolvent Mark TestD
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}



lemma sparsity (x : ℝ) (A : Stores S) (F : Forest S.ratio) (p : Rows.In x A F (G:=G)) :
    let a := fresh x (shots S x) A F (axisPrice p)
    SingleAt a p.1.val.val ∧ ‖a‖ ≤ 1 := by
  intro a
  have h : SingleAt a p.1.val.val := by
    intro i hi
    unfold a fresh; split
    · rename_i he; split
      next hh =>
        have hq : (⟨⟨i,he⟩,hh⟩ : Next.SectorChange.Active A x F) ≠ p.1 :=
          fun eq => hi (congr_arg (fun i : Next.SectorChange.Active A x F => i.val.val) eq)
        rw [on_axis, Pi.single_eq_of_ne hq]
      rfl
    rfl
  refine ⟨h,(pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_⟩
  by_cases hi : i=p.1.val.val
  · rw [hi]; unfold a
    rw [Next.SectorChange.Gap.freshly_read,on_axis, Pi.single_eq_same,OrthonormalBasis.norm_eq_one]
  rw [h i hi,norm_zero]; exact zero_le_one




















end YM.AnalyticBridge.NonflatCovarianceLocality
