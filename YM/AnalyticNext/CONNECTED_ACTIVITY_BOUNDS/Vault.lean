import YM.Analytic.Real
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tablets
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Throne
import YM.Progress.STATIONARY_SCENES.Entrance

/-!
# One exponent letter per operation vs `Plot`

Combining some common-anchor items in *one* exponent (no directions
mingled before squaring). True mandatory algebra. Shift penalty included
not simply paid externally, needs to stay in product. Need global assent
from T for using Grant. Expected charge uses union, not d from one
coordinate summation for another support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Rates Mint
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
  {A p : Stores S} {x : ℝ}

-- one distinct address per anchored group
abbrev Rack (_S : StepData c f) := Signed × (Cell f ⊕ Bond c ⊕ Cell c ⊕ Co c Gain)

def crib (S : StepData c f) (i : Rack S) : Site c := i.1.act (i.2.elim (S.ratio.parent∘Prod.fst)
    (Sum.elim Prod.fst (Sum.elim Prod.fst Prod.fst)))

section terms
variable (T : Tube G S) (U : Config G f) (k : S.Choices) (V : Config G c) (x : ℝ)

-- positive sign convention: subtract in exponent, NOT every row value necessarily positive

def booth (i : Rack S) :=
    let s := i.1; let X := pull s 0 U; let W := pull s 0 V
    let Q := S.prediction X (choice s k); let R := till x; let t := temp x
    weight*i.2.elim (T.workF R X W (fiery G x S.patch.L) t)
      (Sum.elim (T.workI R Q W t) (Sum.elim (fun p => T.workC R W t p+(T.workL R X Q W t p+T.workD R W t p))
        (T.workN R W t)))

-- with true input switches replaced as needed (exact on intact full selection away)
def keptBooth (i : Rack S) := match i with
    | ⟨s, Sum.inl p⟩ => weight * Fextend T x k s p V U
    | ⟨s, Sum.inr t⟩ => booth T U k V x (s, Sum.inr t)

-- weighted by multiplicity only; no stamp yet
def bank (Y : Mint T F A x) (a : ArrayR G f) (i : Rack S) := if crib S i∉A.dome (8*radiusB x) then
      weight*i.2.elim (fun p => crownF T x Y.k i.1 p V (Y.road a))
        (Sum.elim (fun p => crownI T x Y.k i.1 p V (Y.road a)) (fun _ => 0)) else 0

end terms
section stamp
variable (Y : Mint T F A x) (a : ArrayR G f)

def backs (i : Rack S) := bank T Y.V x Y a i

-- Frco: actual shift term per row. D includes weight already.
def dash (i : Rack S) :=
    i.2.elim (fun p => ∑ j : Bool,squareOf (descend (Y.actions Y.μ) (i.1,Sum.inl (p,j))))
        (Sum.elim (fun p => squareOf (descend (Y.actions Y.μ) (i.1,Sum.inr p))) (fun _ => 0))

-- subtract the whole square, add the shift contribution inside the same exponent.
def shell (i : Rack S) := booth T (Y.build a) Y.k Y.V x i - backs Y a i + dash Y i

def pureBooth (i : Rack S) := keptBooth T (Y.build a) Y.k Y.V x i - backs Y a i + dash Y i

def booths (S : StepData c f) (p : Stores S) (d : ℕ) := univ.filter (fun i => crib S i∈p.dome d)

def coverEnergy (p : Stores S) := ∑ i∈booths S p (200*radiusB x), shell Y a i








end stamp
end YM.AnalyticNext.ConnectedActivity.Aff
