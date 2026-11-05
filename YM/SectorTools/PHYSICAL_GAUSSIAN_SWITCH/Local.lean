import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Relative
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Postal

/-!
# Confining the precision AND affine potential displacement
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch
open Function Filter Set Matrix MeasureTheory
open Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment.Relative (trade)
open FreeResolvent
open scoped Topology BigOperators ENNReal Classical
local notation "Covar" => Next.SectorChange.Gaussian.Table

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

namespace Support

def pick (e : J ↪ I) (z : Vec I) : Vec J := z ∘ e
def put (e : J ↪ I) : Matrix I J ℝ := insertion e

omit [Fintype J] [Fintype I] [DecidableEq I] [DecidableEq J] in
lemma pick_cont (e : J ↪ I) : Continuous (pick e) := continuous_pi fun i => continuous_apply (e i)

omit [Fintype J] [DecidableEq J] in
lemma pick_mul (e : J ↪ I) (x : Vec I) : (put e).transpose *ᵥ x = pick e x := by
  ext i; simp [put,pick,insertion,Matrix.mulVec,dotProduct,ite_mul]
lemma pick_put (e : J ↪ I) (x : Vec J) : pick e (put e *ᵥ x) = x := by
  rw [← pick_mul,mulVec_mulVec]; change ((insertion e).transpose * insertion e) *ᵥ x = _
  rw [Shell.pin,one_mulVec]

def VectorOn (e : J ↪ I) (x : Vec I) := ∀ i, i∉range e → x i=0
def SquareOn (e : J ↪ I) (A : Covar I) := ∀ i j, (i∉range e ∨ j∉range e) → A i j=0

lemma restore (e : J ↪ I) {x : Vec I} (hx : VectorOn e x) : put e *ᵥ (pick e x)=x := by
  ext i; by_cases h : i ∈ range e
  · obtain ⟨i,rfl⟩ := h
    exact congr_fun (pick_put e (pick e x)) i
  change ∑ j, (put e i j) * _ = _
  have he j : e j≠ i := fun ht => h ⟨j,ht⟩
  simp [put,insertion,he,hx i h]

lemma retrieve (e : J ↪ I) {A : Covar I} (hA : SquareOn e A) :
    put e * A.submatrix e e * (put e).transpose = A := by
  unfold put
  -- slice_test uses DecidablePred for ranges; prefer classical conventions there
  ext i j
  rw [← Shell.sliced e, Shell.slice_test]
  split
  · rfl
  next h => exact (hA _ _ (not_and_or.mp h)).symm



lemma vector_pick (e : J ↪ I) {x : Vec I} (hx : VectorOn e x) (z : Vec I) :
    x ⬝ᵥ z=pick e x ⬝ᵥ pick e z := by
  nth_rw 1 [← restore e hx]; unfold put; rw [insertion.dot_push]
  congr 1; exact pick_mul ..
end Support
open Support

variable {A D : Covar I} {e : J ↪ I} {a d h : Vec I}

/-- Confining BOTH nonconstant monomials in the density change. This
concerns the inverse covariances and the source in *reference* centered
coordinates, not just which coordinates are shifted. -/
structure ConfinedPrecision (e : J ↪ I) (A D : Covar I) (h : Vec I) : Prop where
  force : SquareOn e (A⁻¹-D⁻¹)
  origin : VectorOn e (A⁻¹ *ᵥ h)

namespace ConfinedPrecision





-- e.g. even nonlocal observables are charged only on this support

end ConfinedPrecision
end YM.SectorTools.PhysicalGaussianSwitch
