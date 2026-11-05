import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Critical
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Tiling
import YM.Progress.CLASSICAL_KIN_RECURSION.Yoke



/-!
# period naturality of real unmasked action and signed thermal extra

Use local log-ratio = sum of logs. Require separately LocalRatio for germ
congruences; globalization of the formula with individual logs not part of
thermal invoice. Tested on actual StepData. No varying calendars
except period parameter c of schedule; needs just Larger c. We ensure all
Boosts of that **same** fixed P,hB etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave.RealSlice
open Lattice RG Precision Tree Bid
open Progress.ClassicalKin Progress.ClassicalKin.Tent Function Wilson
open Push.Uniform
open AnalyticNext.CalendarScene AnalyticNext.CalendarScene.Jets
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} (P:Patch)(K:KernelChoices) {n m:Side}{k:ℕ}
local notation "μ[" n "]" => dock P K n
local notation "τ[" n "]" => shores P n
local notation "T[" n "]" => trees P K n

/-- Real flattened pair. -/
abbrev Desk (P:Patch)(K:KernelChoices)(G:Gauge) (n:Side):=Board (Coarse G) n ℝ × Board (Vertical G P K) n ℝ
abbrev TowerPage (P:Patch)(K:KernelChoices)(G:Gauge) (n:Side) := Board ((Coarse G)⊕(Vertical G P K)) n ℝ

def equip (G:Gauge)(P:Patch)(K:KernelChoices){n:Side}(hn:3≤n.val): Desk P K G n≃L[ℝ] Bid.Dir G n × AxisChart G (trees P K n):=(surfaceIn G n).prodCongr (surfaceCell P K G hn)


def value (p:Clip)(R:PathData G)(hn:3≤n.val): Desk P K G n → ℝ:= uncurry (tested T[n] (label μ[n]) p R) ∘ equip G P K hn

def logShelf (O:ChartRatio G)(R:PathData G){g c:Side}{S:StepData c g}(T:Forest S.ratio)(x:Bid.Dir G c × AxisChart G T):=
    Precision.loop R (lifting T (represent x.1) x.2) - ∑ i:T.Free, Real.log (O.J (x.2 i))

def bonus (O:ChartRatio G)(R:PathData G)(hn:3≤n.val):Desk P K G n→ℝ:=logShelf O R T[n] ∘ equip G P K hn

-- dummy values for tiny tori. No claims of agreement on those.
def titles (p:Clip)(R:PathData G)(n:Side) (i:ℕ): Page (Leaf n (Coarse G⊕Vertical G P K)) i:=
    if h:3≤n.val then iteratedFDeriv ℝ i (value P K p R h ∘ desks (Coarse G) (Vertical G P K) n) 0 else 0
def outro (O:ChartRatio G)(R:PathData G)(n:Side)(i:ℕ) : Page (Leaf n (Coarse G⊕Vertical G P K)) i:=
    if h:3≤n.val then iteratedFDeriv ℝ i (bonus P K O R h ∘ desks (Coarse G) (Vertical G P K) n) 0 else 0
abbrev Ad (G:Gauge)(P:Patch)(K:KernelChoices)(n:Side):= Larger (G:=G) (dock P K n)
lemma value_glue (p:Clip)(R:PathData G)(hn:3≤n.val)(i:ℕ): reprint (value P K p R hn) i=extractF (titles P K p R n (i+1)):=by unfold titles; rw [dif_pos hn]; rfl




section transfer
variable (h:divides n m)(o:Site n)(hm:3≤m.val)(hn:3≤n.val)(W:TowerPage P K G n)
-- exteriors and cell paths commute with tested translations on repeated forest
include h o W

include hm hn



end transfer


end YM.Primitives.TwoWave.RealSlice
