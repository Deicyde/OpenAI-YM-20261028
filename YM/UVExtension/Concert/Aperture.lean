import YM.UVExtension.Concert.Germ
import YM.UVExtension.Wick.Shells
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Embassy

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost Wick Wick.Bower MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ}
open Animals Reserves Gas Ursell Trees Multiple Letter OmitClusters
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
open March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Wick
variable (N : Wick.Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)

abbrev Canvas (x w:ℝ) (ι:Type):= { z: Drums ι // grown x w z }
omit [Fintype ι] in
lemma canvas_nonempty (hx:0<x) (hp:0<w) : Nonempty (Canvas x w ι):= by
  refine ⟨⟨Option.elim' x (fun _=>0),?_⟩⟩; rintro (_|i); exact seat_in hx; exact Metric.mem_ball_self hp

def normal (hx:0<x) (hp:0<w) (hg:w≤g) : Opening (Canvas x w ι) (Vines ι) where
  call p:= hoist p.val
  span:=parade x g
  within p:= marching _|>.2 ⟨p.2 none,fun i=> by rw [show ‖hoist p.val (some i)‖=_ from Complex.norm_real (p.val (some i))]; exact (mem_ball_zero_iff.mp (p.2 (some i))).trans_le hg⟩
  agrees _ _ H G h:= equals_hoist H G hx hp hg (fun x hx=> h ⟨x,hx⟩)

abbrev aperture (_h : Festa Q L H V w g) : Opening (Canvas (betaF G x L) w ι) (Vines ι):= normal (Festa.altitude (H:=H)) _h.margin _h.bound

variable (z: Canvas (betaF G x L) w ι)
abbrev freshen (R:Rep G f) (V:ι→Juice G f):=chunk R (blend V (z.val∘some)) (z.val none)
def roll := (hF.mixture z z.2).some
abbrev fleet (J:(d:Canvas (betaF G x L) w ι)→ Cash W x μ L Q o a T (freshen d R V)) (H:Cash W x μ L Q o a T R): Match.Alliance H (J z) 1 0:= Match.staple rfl rfl rfl
end YM.UVExtension.Concert
