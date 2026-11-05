import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Captains

/-! # Regular script for second unforced log. Keeps repeats. No Hessian subtraction yet!

Anchor on UNION site; pays factor exp surplus at endpoint, doesn't move
 each genealogy to fresh center. Keep honest clustered labels.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained Gas Ursell
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Next.Foundations



namespace Captain
variable (N : Captain H j C' d v Y A b r B q k χ)
variable (p : Clusters H.ThinP) (hX : X.x=s) (hΞ : X.χ=χ) (hK : X.width=o.K)

def stone (i : H.ThinP) := 2^j*(B*N.conduit.meant i.val k)
def design := clusters H.seam N.stone p.snd
lemma stone_pos (i : H.ThinP) : 0≤N.stone i := by unfold stone; have hz:=N.conduit.meant_nonneg k i.val; have hb:=N.balance; positivity
lemma pvc : 0≤ N.design p := clusters_nonneg _ (N.stone_pos) _
include N hX hΞ hK


def reachability (p : Clusters H.ThinP) := unionOf H.smallAt p.snd

def markΦ (p : Clusters H.ThinP) (m : ℕ) :=
    (shiftG s*(1+coverNumber (radiusB s) (reachability (H:=H) p)))^(m*j)*N.design p

end Captain
end YM.ConnectedActivityE6.Blaze.March
