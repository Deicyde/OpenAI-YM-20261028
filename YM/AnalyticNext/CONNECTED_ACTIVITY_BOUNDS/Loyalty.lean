import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Hyssop
import YM.Push.ABSOLUTE_SUMS.Grants

/-!
# Local numerical stencils (all directions)

Full U and V values forced only on actual support of the term. Uniform **kept** and shortened rows,
not assuming cancellation elsewhere. No pulling V logs after unforced guard is dropped.
These utilities are parallel to `FLUCTUATIONS.Locality` but also on D with varying w and cuts,
and here with tag variation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Coverage
open Function Lattice RG Precision Wilson Pressure Pressure.Stores MeasureTheory Push.SectorMeasure
open Matrix Push.SectorMeasure.Oriented Push.AbsoluteSums Tree Next.Fluctuations Filter Win Win.Promise Finset
open Centered Aff Aff.Mint Wages Jewels   Mixed Work.E03 Exterior Bloch
open scoped Topology BigOperators ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {U W : Config G n}

section zone
variable (p : Site n → Site c) (hp : ∀ i j,separation (p i) (p (i+step j))≤1)
include hp
variable {R : ℕ}

lemma faced (x : Cell n) (h : AgreeNear p (p x.1) 4 U W) : faceValue U x = faceValue W x :=
    travel_near p hp U W x.1 _ 4 le_rfl h

variable (P : PathData G) {m : Clip} {x C t : ℝ} {d : ℕ} (hd : 1≤d)
    (h : Bid.LaneCounts P x t m C d p)
include h

lemma kept_rows (i : Site n) (he : AgreeNear p (p i) (radiusB x/50+4) U W) : PathData.kept m t i U ↔ PathData.kept m t i W := by
  have hh {U W : Config G n} (hp' : AgreeNear p (p i) (radiusB x/50+4) U W) (hU : PathData.kept m t i U) : PathData.kept m t i W := by
    intro j; apply le_of_not_gt; intro H
    have hv := h.dropped W i j H
    rw [← faced p hp j (hp'.shrink (by omega))] at H
    exact H.not_ge (hU j)
  exact ⟨hh he,hh fun i hi => (he i hi).symm⟩

include hd

end zone

namespace Shed
section paid
variable {x C : ℝ} {A A' : Stores S} {F : Forest S.ratio} {Y : Mint T F A x} {Y' : Mint T F A' x} {X : Support c}
    (h : Shed F Y Y' X) {P : Teller G} (hT : P.Funds S T) (hC : Optic T x C)

-- Common U,k,V comparisons over an anchored Rack. Use chain outside this file.
include hC



variable {ι v : Type*}

-- helper going reverse variable of matrix. preserve adjacency

omit hC in
lemma backer [Fintype ι] (L : Config G c→ι→v→Pay G) (a : ι → Site c) (b : v → Site c) {p : ℕ} (he : Unseen L a b p)
    {Z W : Config G c} {A B : ι→G.Color} (j : v) (h : AgreeNear id (b j) (2*p) Z W) (hh : ∀ i,separation (b j) (a i) ≤ p → A i=B i) :
    unzip (L Z) A j = unzip (L W) B j := by
  unfold unzip; refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : separation (b j) (a i)≤p
  · rw [he.view _ j _ _ (h.shrink (by omega)), hh i hi]
  have hu : p<separation (a i) (b j) := by rw [separation_comm]; omega
  rw [he.zero i j Z hu, he.zero i j W hu,map_zero]; simp




-- physical pull for supplied halos. use section covariance.
include h hT


end paid
end Shed
end YM.AnalyticNext.ConnectedActivity.Coverage
