import YM.Push.CUTOFF_PROJECTORS.Equations

set_option warningAsError false

/-!
# Actual Wilson equation packets. I: the gradient

Every *positive* torus link, Taylor direction in the `Color` frame of the supplied G. Even coincident site/face reads are differentiated (so this local formula can be used
on any regulator). No inversions of the coupling or `moment` calls in this first check. The sampling/differentiations in subsequent files will start from *this* normalized
gradient; it includes both neighbouring faces for the edge (with signs).
-/

set_option autoImplicit false
noncomputable section

namespace YM.ProjectorNext.Equations
open Lattice RG Wilson Push.CutoffProjectors
open scoped Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators

variable {G : Gauge}

section trace
attribute [local instance] Gauge.frobInner



end trace

section Square





end Square

section gradient

variable {R : Type*} [AddCommGroup R] [One R] {n : Side}





















lemma has_left_link (U : Config G n) (A : Directions G n) (q : Edge (Site n)) :
    HasDerivAt (fun t : ℝ => G.mat (increment U (t • A) q)) (G.colorMat (A q)*G.mat (U q)) 0 := by
  have hh := (Work.G07.smooth_link (G:=G) (k:=0) q).has (l:=[]) le_rfl U A
  rw [Work.G07.left_link] at hh
  simp [Work.G07.linkPrefix,leftDerivs] at hh; exact hh












end gradient
end YM.ProjectorNext.Equations
