import YM.LocalH.Chart
import YM.Push.FREE_RESOLVENT.Views
import YM.Work.F05.Reindex


/-!
# Finite nonwrapping work areas for cut inverse precision jets

Numerical jets on the real tori. Never assuming already computed momentum
estimates. Check offsets at *each* period size before injecting into a whole
kernel claim. Gauge data and choice parameters in the *actual* probes. These
facts let comparisons with irregular forests use transported gauges instead
of postulating shared limits.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set
open Work.F08 Lifted Mark View
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f f' c c' n : Side} {S : StepData c f} {P : Patch} {K : KernelChoices}
variable {R r : ℕ} {s : Signed} {o : Site c} {o' : Site c'}
variable {h : f.val=c.val*P.L.val} {h' : f'.val=c'.val*P.L.val}

section move
variable {X : Type*} {ι ι' : Type*} [Fintype ι] [Fintype ι'] [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {F : pair G c f → ι → ℝ} {F' : pair G c' f' → ι' → ℝ} {u : X →L[ℝ] Vec G c 1} {u' : X →L[ℝ] Vec G c' 1}







end move







-- read affine matrices at corresponding entries across periods
namespace View
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {u : X →L[ℝ] Vec G c 1} {u' : X →L[ℝ] Vec G c' 1}

def alike (u : X →L[ℝ] Vec G c 1) (u' : X →L[ℝ] Vec G c' 1) (o : Site c) (o' : Site c') (R : ℕ) :=
  ∀ x, sees (u x) (u' x) o o' R







end View
end YM.FreeResolvent.Affine
