import YM.AnalyticNext.CALENDAR_SCENE_ADAPTER.FlatCalculation
import YM.Next.BOUNDARY.Derived
import YM.Progress.STATIONARY_SCENES.Thermal


set_option warningAsError false

/-!
# The corresponding quantum rule

§C2lp. Use the SAME recovery as in the
classical result. Remove graph and branch questions from thermal invoice;
works even with all frames, no orientation or Haar-size shortcut (chart
ratio really from issued Survey; don't redeclare it for each period).
Trace formula with *real additive-log coordinate* variations also in pair
variables. This file keeps the input loop kernel and actual measure factor
-- later reductions may pay that/cancel jets under true normalization.
Determinant normalization is *not* additive-log Lebesgue without the chart
piece. No unscaled error or actual α cost shown yet here, and no analytic
disk in post-L units or estimates on varying β.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.CalendarScene
open Filter Function Matrix Lattice RG RG.Supply Bid Tree Exterior Wilson Precision Pressure
open Analysis (D)
open Bloch Progress StationaryScenes Joint
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Jets

section general
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : (E × F) → ℝ} {p : E} {q : F}

lemma along (h : ContDiffAt ℝ ω f (p,q)) (u : F) : D u (fun y => f (p,y)) q = D (0,u) f (p,q) := by
  let j (b : F) := (p,b)
  have he : HasFDerivAt j (ContinuousLinearMap.inr ℝ E F) q :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id q)
  have ht := ((show DifferentiableAt ℝ f (j q) from h.differentiableAt (by simp)).hasFDerivAt.comp q he).fderiv
  change fderiv ℝ (f ∘ j) q u = _; rw [ht]; rfl

lemma adjacents (h : ContDiffAt ℝ ω f (p,q)) (u v : F) :
    J2 (fun y => f (p,y)) q u v = J2 f (p,q) (0,u) (0,v) := by
  have hs : ContDiffAt ℝ ω (fun y => f (p,y)) q := h.comp (f:=fun a => (p,a)) q (contDiffAt_const.prodMk contDiffAt_id)
  rw [← up₂ hs,
    ← up₂ h,Analysis.GermD u (g:=fun y => D (0,v) f (p,y))]
  · exact along (f:=D (0,v) f) (Analysis.dSmooth h _ (by simp)) _
  filter_upwards [(show ContinuousAt (fun y : F => (p,y)) q from
    continuousAt_const.prodMk continuousAt_id).tendsto.eventually (h.eventually (by simp))] with x hx
  exact along hx _


end general

variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {p : Clip} {R : PathData G}

namespace Pair
variable (F : Forest S.ratio) (t : S.Choices) (p : Clip) (R : PathData G)
    (T : Towers S.ratio.count)

/-- Loop and measure terms in the same variables as `tested`. -/
def payload (x : Dir G c × AxisChart G F) := Precision.loop R (lifting F (represent x.1) x.2)
def chart (O : ChartRatio G) (x : Dir G c × AxisChart G F) := Real.log (∏ i : F.Free, O.J (x.2 i))

def charge (f : (Dir G c × AxisChart G F) → ℝ) (i j : Dir G c) :=
    J2 f 0 (inlet F T i) (inlet F T j) + D (0,recovery F p R t T i j) f 0

/-- Vertical pair derivative and one horizontal. -/
def pressure (v : Dir G c) : Matrix (Key F G) (Key F G) ℝ := Matrix.of fun i j =>
    J3 (uncurry (tested F t p R)) 0 (inlet F T v) (0,frame F i) (0,frame F j)

/-- Includes through total degree four in S, and the inverse-mediated S3
terms. No pressure-penalty conventions changed. -/
def tide (v w : Dir G c) : Matrix (Key F G) (Key F G) ℝ := Matrix.of fun i j =>
    J4 (uncurry (tested F t p R)) 0 (inlet F T v) (inlet F T w) (0,frame F i) (0,frame F j) +
      J3 (uncurry (tested F t p R)) 0 (0,recovery F p R t T v w) (0,frame F i) (0,frame F j)

def heatCost (O : ChartRatio G) (v w : Dir G c) :=
    let N := (hessian F t p R 0 0)⁻¹
    charge F t p R T (payload F R) v w +
      (1/2:ℝ)*(tide F t p R T v w*N-pressure F t p R T w*(N*pressure F t p R T v*N)).trace -
        charge F t p R T (chart F O) v w
end Pair

section thermal
variable {ρ : Dir G c → AxisChart G F} {T : Towers S.ratio.count}
    (h : Critical F p R ρ) (t : S.Choices) {η : ℝ}

open Pair (inlet pressure tide recovery chart payload heatCost charge)
include h



variable (hg : Guessed F (installed S.ratio T.A0) ρ)
include hg


omit h hg in
lemma payload_smooth {σ C Λ : ℝ} (hR : R.Bounds p σ C Λ) :
    ContDiffAt ℝ ω (payload F R) 0 := by
  exact loop_smooth hR (A:=fun x : Dir G c × AxisChart G F => lifting F (represent x.1) x.2)
    fun _ => Work.F03.live_smooth F _

omit h hg in
lemma chart_smooth {O : ChartRatio G} (ho : LocalRatio O) :
    ContDiffAt ℝ ω (chart (S:=S) F O) 0 := by
  refine (contDiffAt_prod (f:=fun i (x : Dir G c × AxisChart G F) => O.J (x.2 i)) (t:=Finset.univ) (𝕜:=ℝ)
    (fun i _ => ?_)).log ?_
  · let g (x : Dir G c × AxisChart G F) := x.2 i
    have hh : ContDiffAt ℝ ω O.J (g 0) := ho.germ 0 (Metric.mem_ball_self ho.patch)
    exact hh.comp 0 ((contDiffAt_apply ℝ G.Color i _).comp (f:=Prod.snd) _ contDiffAt_snd)
  · change (∏ i : F.Free, O.J (0:G.Color)) ≠ 0
    simp_rw [ho.anchored]; simp


end thermal
end YM.AnalyticNext.CalendarScene
