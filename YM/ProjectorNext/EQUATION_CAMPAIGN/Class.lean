import YM.ProjectorNext.EQUATION_CAMPAIGN.Gradient

set_option warningAsError false

/-!
# Pre-mask regularity through true link directions

For differentiating group valued stencils before they become labelled coefficients. Keep
an ambient matrix extension (a convenient way to get regularity, not required of later
coefficient records). `OverEntries` concerns the whole torus, gives no support bound,
indicator, or contour estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equations
open Lattice RG Wilson Push.CutoffProjectors
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side}

abbrev Chart (G : Gauge) (n : Side) := Edge (Site n) → G.Mat

def flattenMat (U : Config G n) : Chart G n := fun e => G.mat (U e)

variable {Y Z E : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

def OverEntries (f : Config G n → Y) := ∃ F : Chart G n → Y, ContDiff ℝ ∞ F ∧ f = F ∘ flattenMat

namespace OverEntries
variable {f g : Config G n → Y}



theorem chart (hf : OverEntries f) (U : Config G n) : ContDiff ℝ ∞ (f ∘ increment U) := by
  obtain ⟨F,hF,h⟩ := hf; rw [h,Function.comp_assoc]
  refine hF.comp (contDiff_pi.mpr (fun i => ?_))
  change ContDiff ℝ ∞ (fun A : Directions G n => G.mat (G.lieExp (A i)) * G.mat (U i))
  exact (((G.exp_jet).of_le (by simp)).comp (contDiff_apply ℝ G.Color i)).mul contDiff_const

/-- Iterate derivatives without junk. -/
theorem step (h : OverEntries f) (A : Directions G n) : OverEntries (leftDerivs f [A]) := by
  obtain ⟨F,hF,h⟩ := h
  let L (x : Chart G n) : Chart G n := fun i => G.colorMat (A i) * x i
  have he : ContDiff ℝ ∞ L := contDiff_pi.mpr fun i => contDiff_const.mul (contDiff_apply ..)
  refine ⟨fun y => fderiv ℝ F y (L y), (hF.fderiv_right (by simp)).clm_apply he,?_⟩
  funext U
  have ht : HasDerivAt (fun t : ℝ => flattenMat (increment U (t • A))) (L (flattenMat U)) 0 :=
    hasDerivAt_pi.mpr fun i => has_left_link U A i
  rw [h]
  exact (((hF.differentiable (by simp) (flattenMat U)).hasFDerivAt).comp_hasDerivAt_of_eq 0 ht
    (by rw [zero_smul, Work.G07.at_zero_increment])).deriv

theorem iter (hf : OverEntries f) (l : List (Directions G n)) : OverEntries (leftDerivs f l) := by
  induction l using List.reverseRecOn generalizing f with
  | nil => exact hf
  | append_singleton l a H => rw [Work.G07.left_append]; exact H (hf.step _)

theorem left (hf : OverEntries f) (k : ℕ) : Work.G07.LeftSmooth k f := fun l _ U => (hf.iter l).chart U















variable {ι : Type*}




















end OverEntries
end YM.ProjectorNext.Equations
