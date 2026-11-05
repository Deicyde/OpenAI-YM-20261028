import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import YM.Analysis.Symmetric
import YM.PCalc.Loop


set_option warningAsError false

/-!
# Matrix-chart arithmetic for the rooted & joint equations. No gauge
fixing in coefficient statements. All logs read out on origin germs in
THIS helper. Complement Jacobians & chart radii are not being estimated
via the statements here.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin.Tent
open Lattice RG Laurent Exterior Wilson Precision Tree 
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n c f : Side} {r : Ratio c f} {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {x : X}

def Lamp (x : X) (F : X → G.El) := ContDiffAt ℝ ω (G.mat ∘ F) x
namespace Lamp
variable {U V : X → G.El}


lemma inv (h : Lamp x U) : Lamp x (fun i=>(U i)⁻¹) := by
  simp only [Lamp,comp_def,G.mat_inv]; exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (show ContDiffAt ℝ ω (fun i=>G.mat (U i)) x from h)

lemma lit {w : X→G.Color} (h : ContDiffAt ℝ ω w x) : Lamp x (fun i=> G.lieExp (w i)):= G.exp_jet.contDiffAt.comp x h



end Lamp

def Roof (x : X) (U : X → Config G n) := ∀ i, Lamp x (fun z=>U z i)
namespace Roof
variable {U : X→Config G n}




lemma read (h : Roof x U) (s : Step) (b : Site n) : Lamp x (fun i => s.read (U i) b) := by unfold Step.read; split; exact (h _).inv; exact h _




section slice
variable (B : Forest r) {U : X→ Config G c} {T : X→Config G f}



end slice
end Roof





end YM.Progress.ClassicalKin.Tent
