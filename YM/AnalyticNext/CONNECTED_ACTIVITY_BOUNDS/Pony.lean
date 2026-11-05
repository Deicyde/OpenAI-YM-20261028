import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Hair

/-!
# Incoming E and K

Orders and signatures exact; no support degradation to an arbitrary
ball of that diameter. This analytic part retains E as one letter in
its real masked form. It does NOT prove better than these inherited
weights at future grading/resummation/usage inputs! Hard-core overlap
still on ORIGINAL support even as the PSV cost computed here includes the
mask. In particular K profits from no exponential E->E contraction here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Calls
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

-- nonempty actual contact. No arbitrary witness choice if nonzero.

def hermit (R : Rep G f) (x : ℝ) (S : StepData c f) (i : ℕ) := costE S x (R.activities.reg i).support

def relic (R : Rep G f) (x : ℝ) (S : StepData c f) (i : ℕ) := costE S x (R.activities.forced i).support

def baggage (R : Rep G f) (Y : Mint T F A x) (i : ℕ) (a : ArrayR G f) :=
    - guards Y (priorE S (R.activities.reg i).support) a *
      R.activities.regularOccurrence R.p i (Y.build a)

def heir (R : Rep G f) (Y : Mint T F A x) (i : ℕ) (a : ArrayR G f) :=
    Real.exp (baggage R Y i a) - 1

-- history exact. R activities Valid includes literal extra predicates (fine).
def krill (R : Rep G f) (Y : Mint T F A x) (i : ℕ) (a : ArrayR G f) :=
    guards Y (priorE S (R.activities.forced i).support) a * R.activities.K i (Y.build a)



-- pre-L call, buys both using same r. Note L.Leaf matches heights, P.threshold actual R.Tech


structure PaysBoth (S : StepData c f) (T : Tube G S) (x : ℝ) (R : Rep G f) (A : ℝ) (C' : ℝ) (t s : ℕ → ℝ) : Prop where
  receipt (F : Forest S.ratio) (p : Stores S) (Y : Mint T F p x)
      (i : ℕ) (a : ArrayR _ f) :
    0 ≤ t i ∧ 0 ≤ s i ∧ |heir R Y i a| ≤ t i ∧ |krill R Y i a| ≤ s i
  er : Ac.Hit (hermit R x S) (radiusB x) t A C'
  kr : Ac.Hit (relic R x S) (radiusB x) s A C'
  epos i : 0≤t i
  kpos i : 0≤s i

-- Explicit paired estimates. Radius B(M)>? use no equality of hat radius here.

end YM.AnalyticNext.ConnectedActivity.Calls
