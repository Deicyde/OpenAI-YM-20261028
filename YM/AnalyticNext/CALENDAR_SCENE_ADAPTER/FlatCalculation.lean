import YM.AnalyticNext.CALENDAR_SCENE_ADAPTER.Envelope
import YM.Progress.JOINT_CALENDAR.Issue


set_option warningAsError false

/-!
# Classical descent rule on the purchased finite periods

Reduce the needed higher-order matching estimates to
actual tensor identities on pair variables and next W, no more ρ on
the classical side. Exact order-4 identity including mixed input
positions, needing only A0/tangent and the active literal finite real flat
Hessian inverse (`Service.flat_resolvent` theorem applies directly;
can equally implement a solve by inverting the Hessian -- no other
"propagator" assumed). The impetus to go to other gauges/stacks to
PROVE the bounds at their pre-L orders remains; we don't erase those
forecasts to fit empirical costs on the period. Nor infer period/depth
uniformity of paths from our numerical purchase. Estimate & anchor
lifting remains on the producers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.CalendarScene
open Filter Function Matrix Lattice RG RG.Supply Bid Tree Exterior Wilson Precision Pressure
open Analysis (D)
open Bloch
open Progress  Joint
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Jets

variable {G : Gauge} {c f : Side} {S : StepData c f}

namespace Pair
variable (F : Forest S.ratio) (p : Clip) (W : PathData G) (r : S.Choices)

/-- Actual transform on this tree from the tower's COARSE-to-FINE cross row.
All relative signs in PCalc.Chart unchanged. -/
def inlet (T : Towers S.ratio.count) (x : Dir G c) :=
    (x,relative F (installed S.ratio T.A0) x)

def stress (T : Towers S.ratio.count) (i j : Dir G c) (k : Key F G) : ℝ :=
    J3 (uncurry (tested F r p W)) 0 (inlet F T i) (inlet F T j) (0,frame F k)

/-- True finite Hess, flat on THIS tag, physical chart (unmasked), no
spectral truncation. Well-defined as a formula for estimate requests;
invertibility at all issued scenes in `solves`, below. Includes
empty active matrix. -/
def recovery (T : Towers S.ratio.count) (i j : Dir G c) : AxisChart G F :=
    ∑ k : Key F G, (- ((hessian F r p W 0 0)⁻¹ *ᵥ (stress F p W r T i j)) k) • frame F k

def stressCost (T : Towers S.ratio.count) (i j k l : Dir G c) : ℝ :=
    J2 (uncurry (tested F r p W)) 0 (0,recovery F p W r T i j) (0,recovery F p W r T k l)

def third (T : Towers S.ratio.count) (i j k : Dir G c) : ℝ :=
    J3 (uncurry (tested F r p W)) 0 (inlet F T i) (inlet F T j) (inlet F T k)

def fourth (T : Towers S.ratio.count) (i j k l : Dir G c) : ℝ :=
    J4 (uncurry (tested F r p W)) 0 (inlet F T i) (inlet F T j) (inlet F T k) (inlet F T l) -
      stressCost F p W r T k l i j - stressCost F p W r T j l i k - stressCost F p W r T j k i l
end Pair

section invoice
open Pair (inlet recovery third fourth stress stressCost)
variable {F : Forest S.ratio} {p : Clip} {W : PathData G} {η : ℝ}
  {ρ : Dir G c → AxisChart G F} {T : Towers S.ratio.count}
  (h : Critical F p W ρ) (hg : Guessed F (installed S.ratio T.A0) ρ)

include h

include hg







end invoice

section demand
variable {F : Forest S.ratio} {p : Clip} {W : PathData G} {η : ℝ}
    {ρ : Dir G c → AxisChart G F} {T : Towers S.ratio.count}

-- Use even if paying only diagonal polynomial tests.



end demand
end YM.AnalyticNext.CalendarScene
