import YM.Next.RANK.Radian.Projection
import YM.TraceExtension.Prom.Hill.Promises
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.Next.RANK.Radian.Projection for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice Prayer VectorFourier Finset
open Atlas Normal Perch Wall CellsInt Function
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace

variable {H : Gauge} {P : Schedule} {n k p d L i' : ℕ}
variable (A : AtlasData H P p) {R S Z : ℝ}

end YM.Next.Rank.Radian
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice Prayer VectorFourier Finset
open Atlas Normal Perch Wall CellsInt Function
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace

variable {H : Gauge} {P : Schedule} {n k i p d L : ℕ}
variable (A : AtlasData H P p) {R S Z : ℝ}

-- give Fell receipt
lemma flownSky {P : RG.Levels H} (A : AtlasData H P.S p) (b : ℝ) (n K k : ℕ) (hr : 1≤R)
    (H : ∀ j,Station.middleSky P b k≤ j → j<k→Train A j d R)
    (he : R^(k-Station.middleSky P b k) * 2^d ≤ fraction n K (clim P k))
    (L : ∀ j T,((A.κ k|>.cov j T).re:ℂ)=(A.κ k).cov j T)
    (q : ∀ i j, (((A.κ (Station.middleSky P b k)).cov i j).re:ℂ)=(A.κ (Station.middleSky P b k)).cov i j)
    (C : ∀ i, shutter (wall_chart (fun j=>((A.κ (Station.middleSky P b k)).cov i j).re)))
    (hQ : ∀ i j, |((A.κ (Station.middleSky P b k)).cov i j).re| ≤ fraction n K (clim P k)) : Fell A (Station.beforeSky P b k) d (stretchSky P b k) (fraction n K (clim P k)):=
  ⟨L,q,lit_path A _ H,C,fun _ h=> tracking A _ H _ h,fun x y hp=> (observatory A _ hr H y hp x).trans he,hQ⟩
end YM.Next.Rank.Radian
