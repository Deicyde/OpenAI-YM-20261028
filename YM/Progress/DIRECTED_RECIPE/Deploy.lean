import YM.Next.BOUNDARY.Coordinates
import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2
import YM.Next.FREE_KERNELS.Rack
import YM.Next.SCHEDULE.Blocks
import YM.Progress.DIRECTED_RECIPE.Rollout



/-!
# Putting it on ONE auction

Actual payments from FREE_KERNELS and SCHEDULE. We use the ports below their
last theorems too; e.g., the K used in Directed must be usable WITH the
C3-completed towers built at exactly these prices. No retroactive repinning.
And many tasks still NEED further numerical increases (use ↑pre forecasts,
V : Delays T input etc.), besides actually proving in-situ estimates for the
real objects.

At `engage` take `Kin.Planned` for that very chosen Horizon. Its existence has
not been proved. Use any instance purchased by producers after these gates,
keeping their strengthening at call sites. Origins and Invoices THEN wanted
on the same choices; these are downstream proof obligations discussed in Bands
(not independent inputs to making the Directed, no claim of generic estimates
on all Wills). Precisely exhibit the calls and their orders; don't encode a
paper gallery of alternative pellets/paths/levels and add an assumption later
that the bids agree. Nothing chooses beta waits or analytic widths *from*
the cutoff masses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe
open Function Set RG Wilson Lattice RG.Shoot Ovens Ovens.Pipes Input Precision
open Next.Scheduling RG.Supply MeasureTheory Pressure
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

section machines
variable {G : Gauge} {a : Levels G} {M : Horizon a} {O : ChartRatio G}
variable {s : Survey G} {K : MapPrices} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
    {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y} {B : Beam K D}
variable {e : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage}

/-- For YU route. The whole Alloy indexed by the SAME stamp quotations as used
by scheduling. (Witness; taking prices after fixing the preliminary survey.) -/
def alloy (k : Kin M s.B.chart) (r : Permissions a) (paid : Paid I a)
    (tax : Regime B e F W) (hM : M.Suffices K)
    (hk : k.Planned (B.price F)) : Org.Alloy (s.metals q K v) D :=
    ⟨B.price F,T,W,Y,I,tax.prices,prepared k e F r paid hM s.B.chartRatio hk⟩

/-- Even when using `design`, don't forget surviving history when
requiring this B from `Bolt`. Let all consumers depend on the whole Fired data. -/
theorem drives (hg : G.Simple) (paid : Paid I a) (tax : Regime B e F W) (hM : M.Suffices K)
    (k : Kin M s.B.chart) (hk : k.Planned (B.price F)) (r : Permissions a)
    (hc : Origins k r) (hw : Invoices k e F r) :
    let A := alloy k r paid tax hM hk
    ∃ J, (∀ N p, Fired k e F r N 0 p (J N p)) ∧ ∃ b : Org.Bolt A,b.history=seriesOf a J ∧
      ∀ C : Family G,C.path=A.B.bake.make b.history → Spec.Calibrated C := by
  intro A
  obtain ⟨hO,hP,J,HF,Hr,HT,hm⟩ := design paid tax hM s.B.chartRatio hk hg hc hw
  refine ⟨J,HF,⟨hP,seriesOf a J,Hr,HT,hm⟩,rfl,fun C he => ?_⟩
  exact ⟨_,_,_,_,_,_,_,_,_,A.B, seriesOf a J,Hr,he,hm⟩


end machines

section scheduling
variable {G : Gauge}

/-- A preliminary Survey port; places ANY costs now of these shapes. `Prebase`
is imposed before Rolls (s.floorL≥b, s.X Catalog, clip direct caps; can just
increase floor later with similar conditions if changing). No nonlinear
purchase asserted. -/
structure Prebase (s : Survey G) (l γ : ℕ → ℝ) (b : ℕ → ℕ) : Prop where
  beam : Next.Free.Catalog s.B.kernel s.X l γ b
  enough : b ≤ s.floorL
  prices : s.direct ≤ γ

-- Nonempty setting for the numerical receipts -- not a promise that, say,
-- the clips of THIS survey will pass any required nonlinear pricing.


variable {s : Survey G} {K : MapPrices} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
    {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y} {B : Beam K D}
variable {e : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage} {a : Levels G} {l γ : ℕ → ℝ} {b : ℕ → ℕ}

/-- Retain the towers through this path. If purchasing further capabilities on
Horizon, ensure present BEFORE invoking Kin or assembling Directed. -/
structure Sponsored (s : Survey G) (l : ℕ → ℝ) (K : MapPrices) (A H : Horizon a) : Prop where
  rack : Craft.Rack a s.X A
  original : Next.Free.Present a A l
  retain : Bid.Retained H A
  plan : H.Suffices K
  final_price : Next.Free.Present a H l
  chosen N m n : m≤N → Bid.Sworn (H.H N m) n G



open Next.Scheduling.Weak




end scheduling
end YM.Progress.DirectedRecipe
