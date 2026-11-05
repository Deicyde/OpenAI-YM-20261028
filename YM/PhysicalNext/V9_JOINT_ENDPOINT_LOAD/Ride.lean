import YM.Extra.SOURCE_HISTORIES.Reserve
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.AtPose
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Reverse
import YM.Planned.ATOM_FORCED_ESTIMATE.Vacuum
import YM.Progress.STATIONARY_SCENES.Entrance
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Backwards
import YM.Push.STRESS_FLUX.Line
import YM.Push.STRESS_FLUX.Weak
import YM.SectorNext.VACUUM_NORMALIZATION.Pivots
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Campaign


/-!
# SAME-Z² payments and transferring from two alternative normalized laws

`switched`: physical window changes on altered subset of columns (e.g.
mid vs whole-endpoint comparison) applied directly to the word, retaining the
ordered-mean difference INSIDE its whole evaluation in paying. `inserted`:
quadratic/affine signed Frco exponent restricted to any slots selected on that
same kernel, positive p-precision and comparison on inserting this potential
with explicit normalization. Uses even if separating different portions of
that correction from ones left in single-address expansion. These are **moment**
statements, do not modify any density identity or move a word's support or claim
it represents the multiplier of that same expansion after a new kernel is
issued; the ancillary bounds must hold on the ORIGINAL field. See also annulus
application without any kernel shift/tilt/restriction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad
open Function Filter Metric Set Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian Spot Spot.Programme Notice Tariff
open SectorTools.PhysicalGaussianInsertion (maskForm maskVec Inserted)
open SectorTools.PhysicalGaussianInsertion.Physical
open SectorTools.PhysicalGaussianSwitch.Mosaic (centerNew covNew)
open MeasureTheory Push.SectorMeasure Presented Wisps Schur Bid  Matrix
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius ENNReal

structure Boats where
  w : Switch.Fare
  rate : ℝ
  base : ℝ
  rate_pos : 0<rate
  base_pos : 0<base

variable {G : Gauge} {c f : Side} {S : StepData c f} {d : Desk G S} {Q : Kiosk} {W : Boats} {Pt : Teller G}
    {Z : ChartRatio G} {χ : Chi} {θ E x r : ℝ} {k n power : ℕ}
    {ι H R α β γ : Type} [Fintype ι] [Fintype H] [Fintype R] [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ]
    {A : Stores S} {F : Forest S.ratio} {κ : S.Choices} {V : Config G c} {X : Support c}
    {l : Viewport (spectacle d A F κ) X H R ι} {D : (spectacle d A F κ).Slices} {b : Finset ℕ} {q : Programme D b} {z : q.Run α β γ}
    {s : Seats l z} {a : Notice l} {B : Reading a z} {M : Income α β γ (H⊕R)}

def maskPrice (w : Boats) (x : ℝ) (m : ℕ) := Real.exp (w.base * rate (-w.rate) (radiusB x) * m)

structure Trip (d : Desk G S) (w : Boats) : Prop where
  swaps (A : Stores S) (F : Forest S.ratio) (κ : S.Choices) (V : Config G c) : A.flags=RG.flags (temp d.betaHat) V →
    Switch.Return w.w 2 d.betaHat d.tube A F V κ ∧
    ∀ (y : LinkArray G (Frozen A d.betaHat F)) (U : Finset (In (G:=G) d.betaHat A F)),
      book d.tube d.betaHat V κ A F d.broadCut d.radius y d.g U 2 (maskPrice w d.betaHat U.card)

theorem boats (G : Gauge) (P : Patch) (Pt : Teller G) (hP : P.Branches Pt.bind G) (r : ℝ) (hr : 0<r) : ∃ W : Boats,
    ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=P → ∀ (d : Desk G S) {Z χ power θ E k n Q},
      Calling Pt Z χ power r x d → Day Q θ E k n d → Trip d W := by
  obtain ⟨s,C,hs,hC,h⟩ := bands 2 one_le_two P Pt hP r hr
  obtain ⟨w,hw⟩ := Switch.post 2 G P Pt hP
  refine ⟨⟨w,s,C,hs,hC⟩,?_⟩
  filter_upwards [h,hw] with x hx hw
  intro c f S hS d Z χ power θ E k n Q hC hd
  constructor; intro A F κ V hV
  obtain ⟨hr,hP,rfl,hβ,hD,-,-,-,-⟩ := hC
  rw [hS] at hβ hD
  exact ⟨hw S d.tube hS hd.larger hr hP A F V κ hV, fun y U => hx S d.tube hS hr hP V κ A F hV d.broadCut d.input.beta
    d.radius hd.beta hβ.2 hd.radius hD.le y U⟩

namespace Day
variable (h : Day Q θ E k n d) (hw : Trip d W) (hC : Clearing (spectacle d A F κ) V) (o : Site c) (hT : Terms s V) (hA : Ancillary B M s θ V)
  (y : LinkArray G (Frozen A d.betaHat F)) (U : Finset (In (G:=G) d.betaHat A F))
include h hw hC hT hA




end Day
end YM.PhysicalNext.JointLoad
