import YM.AnalyticBridge.RESET_INCOME_PORT.Quote
import YM.AnalyticBridge.RESET_INCOME_PORT.Sheen

set_option warningAsError false

/-!
# Example local input prices for Coupon.Uses

At matched A,k,V. Don't require any raw plot testing beyond what a pointwise
estimate would itself need at the same `screen` (e.g., to prove `lineOK`
at any mask edge on b). Prices use the actual β, flags, all hats and all
paths incl oriented tail signs. *Field prices* per plate address; no claim
per-unit prices persist on the outputs of an arbitrary map; not saying that
these row estimates can be earned on all assembled formulas. Here one unit
is, e.g., a T.workF anchor/charge after applying already bought cancellations
(possibly winding table with all tags kept), not claiming support at the
single face. E-Journal cells need their own support-priced estimates. These
order-zero per-row comparisons may couple or bill the output contribution
there with either bank/curve hypothesis. All are actual prices in the
specified evaluation formula. Log stand tests use sheen lemma on the true
regular J; no log of guard needed.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 256
noncomputable section
namespace YM.AnalyticBridge.ResetIncome

open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

namespace LinePrice
variable {G : Gauge} {c f : Side} {S : StepData c f}

abbrev Tag (c f : Side) := Cell f ⊕ Bond c ⊕ Cell c ⊕ (Bloch.Co c Gain) ⊕ Site f

variable (e : Plate G S) (A : Stores S) (R : Rep G f) (V : Config G c) (k : S.Choices)

def grain (z : e.Sample A) (s : Signed) : Tag c f → ℝ :=
  let b := R.beta
  let x := e.x
  let C := (shots S x)
  let T := e.tube
  let p := till x; let t := temp x
  let U := pull s 0 (e.image R A V k z); let B := pull s 0 V; let Q := S.prediction U (choice s k)
  let l := (e.center A V k z.1 + coupling b • z.2)
  Sum.elim (fun i => -b * (T.workF p U B (fiery G x S.patch.L) t i -
    ∑ y : Bool, chargedUp T x V k C A e.forest e.chip e.d z.1 l s (i,y)) - b*cuff R.path R.clip R.p 1 p U i)
    (Sum.elim (fun i => -b*(T.workI p Q B t i-chargedSide T x V k C A e.forest e.chip e.d z.1 l s i))
      (Sum.elim (fun i => -b*(T.workC p B t i+T.workL p U Q B t i+T.workD p B t i)+
        b*cuff T.down T.low e.point S.patch.L.val p B i)
        (Sum.elim (fun i => -b*T.workN p B t i) (fun i => -b*(PathData.atomSeries R.path.cubic R.p U i+
          PathData.atomSeries R.path.quartic R.p U i) - PathData.atomSeries R.path.loop R.p U i))))

abbrev Rack (A : Stores S) := (Signed × Tag c f) ⊕ Rows.Receipt G S ⊕ Rows.In e.x A e.forest (G:=G)

def lines (z : e.Sample A) : Rack e A → ℝ :=
  let v := e.tube; let g := coupling R.beta; let q := e.center A V k z.1
  let y := direct v e.x V k (shots S e.x) A e.forest e.chip e.d z.1 q
  Sum.elim (fun i => (Fintype.card Signed:ℝ)⁻¹ * grain e A R V k z i.1 i.2) (Sum.elim
      (fun i => -(y i*y i / 2)/g^2) (fun i => eta v e.x V k (shots S e.x) A e.forest e.chip e.d z.1 q g i * z.2 i))

def shudder (z : e.Sample A) := z.2 ⬝ᵥ (((e.Cov A V k)⁻¹ - e.Gram A V k) *ᵥ z.2) / 2



def notes (z : e.Sample A) i := -R.activities.regularOccurrence R.p i (e.image R A V k z)





variable {A e}
/-- Labels with honest address and finite β. Remaining response
income after providing these costs: there are *also* missing mass &
relative error tests on the signed multiplier, not implied by even
these hypotheses. -/
structure Tune (e : Plate G S) (A : Stores S) where
  track : e.Sample A → Rack e A → ℝ
  ntrack : e.Sample A → ℕ → ℝ
  pure : e.Sample A → ℝ
  spends : e.Sample A → Rack e A → ℝ
  rents : e.Sample A → ℕ → ℝ
  assess : e.Sample A → ℝ

namespace Tune
variable (t : Tune e A) (Y : Sheen.Gloss e.chart) (w : Quote) (u : ℝ)





/-- Point estimates on orientation/channel/label units at that one z's
actual calls, plus the explicit quadratic. These are pointwise on the
Sample, not assuming response of any other sector or across changing
allocations (hence no measurability claims here). -/
structure Checks (z : e.Sample A) : Prop where
  dial i : |lines e A R V k z i-t.track z i| ≤ t.spends z i
  each i : |notes e A R V k z i - t.ntrack z i| ≤ t.rents z i
  residual : |shudder e A V k z - t.pure z| ≤ t.assess z
  costs : Summable (t.rents z)







end Tune
end LinePrice
end YM.AnalyticBridge.ResetIncome
