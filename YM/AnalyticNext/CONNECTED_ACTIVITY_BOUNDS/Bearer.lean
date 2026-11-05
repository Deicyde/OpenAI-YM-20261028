import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Arctic
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Filaments
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Hundreds
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Pocket
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Pony
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tub
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Wick
import YM.Progress.STATIONARY_SCENES.SliceGap
import YM.Push.RELAY_DIFFERENCE.Applications
import YM.Push.SECTOR_MEASURE.Presented



/-!
# Assembling on the *operated* objects, spine of the activity alphabet

All inherit queries run against these data. F and Y handed down
coherently; no resampling in products. Intended as ingredients for
first gas. Costs spent on all rotations, old multipliers included.
Not taking an output E or K inequality as an input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Cab
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Paths Chains Calls
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

-- names for later GPA. `Back` all inherited other than K. Up and down
-- eps powers kept separate. Cube contacts use 500B for packets.
abbrev Atoms (f : Side) := Lamps f ⊕ Lamps f ⊕ Lamps f
abbrev Tails (c f : Side) := Buttons f ⊕ Buttons c
abbrev Back (c f : Side) := ℕ ⊕ (Atoms f ⊕ Tails c f)
abbrev LocalStep (S : StepData c f) := (Bg S ⊕ Flick S) ⊕ (Chains.Year S ⊕ Bond f)
-- exactly-one/exponent choices, K set chosen elsewhere
abbrev May (S : StepData c f) := Back c f ⊕ LocalStep S
abbrev Other (S : StepData c f) := ℕ ⊕ May S
abbrev Tab (S : StepData c f) := Mixed.Alphabet S (Other S)
section body
variable (T : Tube G S) (x W : ℝ) (R : Rep G f) (N : ChartRatio G)

def pAtoms := Sum.elim (article R.path.loop S x) (Sum.elim (article R.path.cubic S x) (article R.path.quartic S x))
def pTails := Sum.elim (rib R.path S.ratio x) (rib T.down (plain c) x)
def pBack := Sum.elim (hermit R x S) (Sum.elim (pAtoms (S:=S) x R) (pTails T x R))
def pStep (S : StepData c f) := Sum.elim (Sum.elim (roomies (S:=S) x) (Jewels.column S x))
    (Sum.elim (allot S (radiusB x)) (televised S x))
def pMay := Sum.elim (pBack T x R) (pStep x S)
def pOther := Sum.elim (relic R x S) (pMay T x R)

def atoms (Y : Mint T F A x) (z : ArrayR G f) :=
    let b := Aff.weight; let v := R.beta*b; let a := cashB Y R.beta z
    Sum.elim (fun i => atomic R.path.loop R.p b Y i a)
      (Sum.elim (fun i => atomic R.path.cubic R.p v Y i a) (fun i => atomic R.path.quartic R.p v Y i a))

def tails (Y : Mint T F A x) (z : ArrayR G f) : Tails c f → ℝ :=
    let β := R.beta; let a := cashB Y R.beta z
    Sum.elim (fun i => Real.exp (cuts i R Y a)-1)
      (fun i => Real.exp (reset i x β T Y.V)-1)

def back (Y : Mint T F A x) (z : ArrayR G f) : Back c f → ℝ := Sum.elim
    (fun i => heir R Y i (cashB Y R.beta z)) (Sum.elim (atoms T x R Y z) (tails T x R Y z))

def memory (L : Finset ℕ) (Y : Mint T F A x) (z : ArrayR G f) : LocalStep S → ℝ :=
    let a := cashB Y R.beta z
    Sum.elim (Sum.elim (chip Y R.activities L W a) (slash Y R.beta N a))
      (Sum.elim (fun p : Year S => chain Y p z) (fun p : Bond f => snapSale Y p R.beta z))
def may (L : Finset ℕ) (Y : Mint T F A x) (z : ArrayR G f) := Sum.elim (back T x R Y z) (memory T x W R N L Y z)
def other (L : Finset ℕ) (Y : Mint T F A x) (z : ArrayR G f) := Sum.elim
    (fun i => krill R Y i (cashB Y R.beta z)) (may T x W R N L Y z)

def reach := Mixed.foot S 500 (radiusB x) (pOther T x R)

def leaf (L : Finset ℕ) (Y : Mint T F A x) (z : ArrayR G f) : Tab S → ℝ := Sum.elim
    (fun p => pact p R.activities L R.beta W N Y (cashB Y R.beta z)) (other T x W R N L Y z)
end body

-- local tilt passport for one-step v.Height hands
section ticket
variable {ι v : Type*}

abbrev Surface (T : Tube G S) (x : ℝ) (ι : Type*) := ∀ (A : Stores S) (_L : Finset ℕ) (F : Forest S.ratio),
    Mint T F A x → ArrayR G f → ι → ℝ

-- L STILL from word, so permit every choice while charging. common ε t.
-- Doesn't purchase any RECURSIVE seat beyond first-integrated use.
structure Token (T : Tube G S) (x r : ℝ) (t : Till) (w : ι → Tilt (Vars G f)) (g : Surface T x ι)
    (p : ι → Support c) (a Z Q : ℝ) : Prop where
  sound (A : Stores S) (L : Finset ℕ) (F : Forest S.ratio) (Y : Mint T F A x) (z : ArrayR G f) : cert S x A Y.V →
    Y.u=holdSize G S.patch x → Y.r=r → ∀ i, ‖g A L F Y z i‖ ≤ Ticket (w i) z
  positive i : (w i).Sound
  fund : Ac.Hit p (radiusB x) (fun i => sale t (w i)) a Z
  tilt i (s : Finset ι) : ∑ j∈s,(w j).tally i ≤ Q

namespace Token
variable (T : Tube G S) {r x a Z Q : ℝ} {t : Till} {w : ι → Tilt (Vars G f)} {g : Surface T x ι} {p}



-- helpers to pay any rank

end Token
end ticket

-- Band budgets on this T to request the theorem. Exposure proof from
-- Lives downstream can furnish from the true record.
structure Client (P : Teller G) (T : Tube G S) (R : Rep G f) (Z a : ℝ) (x : ℝ) : Prop where
  fits : Presented.Fits T R x
  band : OnBand G S.patch x R.beta
  leg : R.p.B ≤ 2*radiusB x
  pre : reserve R.p.supportExponent a (conversion S.ratio 125) Z
  cost : ∃ Λ L M : ℝ,R.Lawful P.top.width P.top.paths Λ L M ∧ Λ ≤ betaF G x S.patch.L^(1/8:ℝ) ∧
    L ≤ amend G S.patch x (1/2) ∧ M ≤ amend G S.patch x (1/2)
end YM.AnalyticNext.ConnectedActivity.Cab
