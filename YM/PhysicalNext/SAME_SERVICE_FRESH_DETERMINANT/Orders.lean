import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.Next.SCHEDULE.Layers
import YM.Next.STATIONARY.Level.Recurse
import YM.Next.STATIONARY.OneLoop.Bubbles
-- Adj


/-!
# Prices for the determinant, NOT a new price type required of further producers

Records just to remember a pair of calls into YM.Next.STATIONARY
sharpened at the L^4 step; used to show adequacy on the *existing*
price types. Use both j→j and j→j-1. Kernel penalty and MapPrices
known; use the direct Clip bound 1 of Survey (if different in another
campaign, make it another parameter). No need for later periods or the
width and cost of some particular Ticket, nor one actually chosen Roll
in the proof of `docket`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.SameDet
open Function Filter Lattice RG RG.Supply Wilson Precision Bid Next.Scheduling

/-- j first (inlet smoothing index), i destination. `bill` quotes mesh
price after L; no growth requirement on that one. `det` is instead pre-L. -/
structure Tags where
  Lmin : ℕ
  det : ℝ
  det_ge : 1 ≤ det
  slope : ℝ
  slope_ge : 0 ≤ slope
  bill : Side → ℝ
  expn : ℝ
  expn_pos : 0 < expn

open Stationary

def Pays (G : Gauge) (k : KernelChoices) (K : MapPrices) (j i : ℕ) (s τ a : ℝ) (F : Tags) : Prop :=
    ∃ κ : ℝ, Transition G k j (K.η j) (K.α j) (pacesE K j) 1 (K.α i) (pacesE K i) 1 a τ κ F.slope s F.expn F.Lmin F.bill
        (fun L => F.det*(L.val:ℝ)^4)

/-- WIDTH ask certified before input widths and classical caps. -/
structure Office (G : Gauge) (k : KernelChoices) (K : MapPrices) where
  s : ℕ → ℕ → ℝ
  opens j i : 0 < s j i
  asks j i τ a : 0<τ → 0≤a → ∃ F : Tags, Pays G k K j i (s j i) τ a F



/-- AFTER the actual inlet widths & classical path ceilings, still before L. -/
structure Relays {G : Gauge} {k : KernelChoices} {K : MapPrices} (Y : Office G k K)
    (τ a : ℕ → ℝ) where
  fees : ℕ → ℕ → Tags
  earns j i : Pays G k K j i (Y.s j i) (τ j) (a j) (fees j i)

variable {G : Gauge} {k : KernelChoices} {K : MapPrices}


end YM.PhysicalNext.SameDet
