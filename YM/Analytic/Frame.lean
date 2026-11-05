import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Matrix.PosDef
import YM.Analytic.Implicit
import YM.PREC.Pred


/-!
# Local stationary branches for the actual finite frame score

The frame value at the patch center is fixed to one. The remaining frame
coordinates use the native physical color Lie chart. We apply the recovered
positive-Hessian implicit-function theorem to the existing `Patch.score`,
with fine-field input `Push.product` exactly as in the native frame branch.

This is a local fixed-period theorem. Analyticity, stationarity and positive
vertical Hessian of this actual score are explicit hypotheses. No uniform
radius, global-minimizer identification or Wilson estimate is asserted.
-/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace YM.RG.Patch

abbrev FrameCoordinates (P : RG.Patch) (G : Gauge) :=
  EuclideanSpace ℝ ({i : P.Points // i ≠ P.center} × G.ColorIndex)

def frameFromCoordinates (P : RG.Patch) (G : Gauge) (q : P.FrameCoordinates G) : P.Frame G := by
  classical
  exact fun i => if h : i = P.center then 1 else
    G.lieExp (WithLp.toLp 2 fun j => q (⟨i,h⟩,j))

@[simp] theorem frameFromCoordinates_center (P : RG.Patch) (G : Gauge)
    (q : P.FrameCoordinates G) : P.frameFromCoordinates G q P.center = 1 := by
  classical
  simp [frameFromCoordinates]

end YM.RG.Patch

namespace YM.Analytic

open Lattice RG
variable {G : Gauge} {c f : Side} (S : StepData c f) (y : Site c)

def nativeFrameScore (q : Push.In G f × S.patch.FrameCoordinates G) : ℝ :=
  S.patch.score (Push.product S y q.1) (S.patch.frameFromCoordinates G q.2)

/-- A genuine analytic local stationary branch of the existing finite frame score. -/
theorem native_frame_stationary
    (q₀ : S.patch.FrameCoordinates G)
    (ha : AnalyticAt ℝ (nativeFrameScore S y) (0,q₀))
    (hs : HasFDerivAt (fun q => nativeFrameScore S y (0,q))
      (0 : S.patch.FrameCoordinates G →L[ℝ] ℝ) q₀)
    (hp : ∀ v : S.patch.FrameCoordinates G, v ≠ 0 →
      0 < iteratedFDeriv ℝ 2 (fun q => nativeFrameScore S y (0,q)) q₀ ![v,v]) :
    ∃ branch : Push.In G f → S.patch.FrameCoordinates G,
      branch 0 = q₀ ∧ AnalyticAt ℝ branch 0 ∧
      (∀ a, S.patch.frameFromCoordinates G (branch a) S.patch.center = 1) ∧
      ∀ᶠ a in 𝓝 0, HasFDerivAt (fun q => nativeFrameScore S y (a,q))
        (0 : S.patch.FrameCoordinates G →L[ℝ] ℝ) (branch a) := by
  obtain ⟨branch,hb,ha,hstat⟩ := param (nativeFrameScore S y) (0,q₀) ha hs hp
  exact ⟨branch,hb,ha,fun _ => RG.Patch.frameFromCoordinates_center _ _ _,hstat⟩

end YM.Analytic
