import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Push.FREE_RESOLVENT.Differentiated
import YM.Push.FREE_RESOLVENT.Torus
import YM.Push.SECTOR_MEASURE.Cells
import YM.Work.E01
import YM.Work.E07.Scale


set_option warningAsError false

/-!
# Literal REAL normalized t' direction currency of  etc.

For ordered exp-log chart derivatives, not yet the left Lie derivative
transfer. From the stronger positional payments keep small-factor exponents,
including jointly with the exponentially small comparison price. A fixed-order
statement; buy for the orders before deploying. This extra temperature condition
as with gaps only reaches the booked purposes after an *actual* delay.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree Matrix
open YM.Push.SectorMeasure    Metric   
open   FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent (native Bundle Cost)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k : ℕ} {σ d r C x η g b u : ℝ}
variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable {p : ι → Site c} {q : κ → Site c} {F : Directions G c → Matrix ι κ ℝ} {B : Directions G c}

/-- The extra threshold for E:t t  comparison; not another direction-scale
rule in row formulas. -/
def Cash (G : Gauge) (L : Side) (x : ℝ) := 0 ≤ temp x ∧ temp x ≤ 1 ∧ temp x ≤ 2 * fiery G x L
lemma earning (G : Gauge) (L : Side) : ∀ᶠ x : ℝ in atTop, Cash G L x := by
  filter_upwards [Work.E07.temp_coarse_le G L, Work.E01.fiery_le G L 2,
    (Work.E01.largeT_tendsto G L).eventually (ge_mem_nhds zero_lt_one)] with x hx hy ht
  exact ⟨temp_nonneg _,hx.trans (hy.trans ht),hx⟩




def tollUnit (G : Gauge) (L : Side) (x : ℝ) (n : ℕ) := if n=0 then (1:ℝ) else fiery G x L



def Bends (o : Site c) (l : List (Directions G c)) (x : ℝ) (P : ℕ) :=
  ∀ i ∈ l, ∀ e, ‖i e‖ ≤ temp x*(1+(separation e.1 o:ℝ))^P


def Issued (p : ι → Site c) (q : κ → Site c) (F : Directions G c → Matrix ι κ ℝ) (B : Directions G c)
    (L : Side) (P : ℕ) (d C x : ℝ) (l : List (Directions G c)) :=
  ∀ (o : Site c), Bends o l x P →
    Bill (radial (Directions G c) (native c) o P) (native c) p q l d
      (C*tollUnit G L x l.length) (jet id F l B)




-- to produce simple charges retaining arc power


-- Literal issue on same `Sky`, includes reading the estimate on window
-- precision itself and its residual concurrently.

end YM.AnalyticBridge.Covariance
