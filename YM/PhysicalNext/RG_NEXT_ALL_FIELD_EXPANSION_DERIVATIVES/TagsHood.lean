import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsColumnL

/-! Trees: generalize E6/Hood reasoning to **changing forests**, including active, lens and invitations. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio}
variable {x : Site c} {p : Bond f} {X : Coat T F} {X' : Coat T F'} {a d : ℕ} {η r Q Y : ℝ}
variable {R : Rep G f} {Z Z' : Support c} {k k' : Finset ℕ} {w v : Air f G}

structure DistrictView (X : Coat T F) (X' : Coat T F') (Z : Support c) : Prop where
  weather : X.x=X'.x
  width : X.width=X'.width
  chi : X.χ=X'.χ
  places (y) (he : y∈Z) : y∈X.seeds.place ↔ y∈X'.seeds.place
  frames p (hp : atEdge S p ∈ Z) : F.drape X.Y p=F'.drape X'.Y p
  trunks p (hp : atEdge S p∈Z) : p∈F.trunks ↔ p∈F'.trunks
  site y (hp : y∈Z) : X.k.1 y=X'.k.1 y
  bond p (hp : p.1∈Z) : X.k.2 p=X'.k.2 p
  actual : Agrees Z X.V X'.V

structure ForestLocale (X : Coat T F) (X' : Coat T F') (Z : Support c) (w v : Air f G) (k k' : Finset ℕ) (R : Rep G f) : Prop extends
    DistrictView X X' Z where
  airs (p : Tubular f G) (he : p∈podium S G Z X.B) : w p=v p
  covering (i : Site f) (he : S.ratio.parent i ∈ Z) : i∈Contract.covered R k ↔ i∈Contract.covered R k'





namespace ForestLocale
variable (h : ForestLocale X X' Z w v k k' R) (hk : Room P S T X.x)
include h
lemma B : X.B=X'.B := congr_arg radiusB h.weather




include hk








end ForestLocale
end YM.ConnectedActivityE6
