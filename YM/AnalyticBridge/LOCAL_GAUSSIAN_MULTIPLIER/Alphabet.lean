import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Pages
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Stratum

/-!
# Assembly from Slices. Exact multiplier before expansion

Guards mismatched V-inventory at the outside. Tsum here over choices
of K addresses, even if K-parent, same overlap/eligibility/ownership
on the physical inputs as Sector.density. Log alphabet requires
unconditional HasSum on the real series. Includes log(J(a)), with its
broad extension (broad door gates included separately).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision Exterior Bloch MeasureTheory Next.SectorChange Next.SectorChange.Gaussian
open Next.SectorChange.Rows YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Next.Fluctuations.Sector
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff InnerProductSpace Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S}
namespace Spot
variable (u : Spot d)

/-- The log alphabet. Different indexes even if zero prices. -/
abbrev Log := RowPosts c f ⊕ (u.ActiveKey ⊕ u.Relative ⊕ u.Correction ⊕ BasePosts c f ⊕ ℕ)

def lacquer (V : Config G c) (p : u.Visual) (i : u.ActiveKey) :=
  logGuard d.broadCut d.chart d.radius (displaced (u.m V p.1) d.g p.2 i)

def back (V : Config G c) (p : u.Visual) := -averaged (fun s => reduced d.input
    (till d.betaHat) (pull s 0 (u.hard V p))) + coarseTail d.tube d.betaHat d.out V d.input.beta



def price (D : u.Slices) (j : u.Log) (V : Config G c) (p : u.Visual) := match j with
  | .inl i => u.residualFee V p i
  | .inr (.inl i) => u.lacquer V p i
  | .inr (.inr (.inl i)) => u.book D V i
  | .inr (.inr (.inr (.inl i))) => u.cardCost D V p i
  | .inr (.inr (.inr (.inr (.inl i)))) => u.basePost V p i
  | .inr (.inr (.inr (.inr (.inr i)))) => -d.labels.regularOccurrence d.input.p i (u.hard V p)

def sumValue (V : Config G c) (p : u.Visual) := (-d.input.beta*averaged (u.bolt V p)) +
    ((∑ i, u.lacquer V p i)+(u.receipt V+(u.affinity V p+(u.back V p + -d.labels.additive d.input.p (u.hard V p)))))

/-- HasSum on the real logs, when in the named actual sector, not only
at flat. -/
theorem repository (D : u.Slices) (V : Config G c) (h : u.Clearing V) (hv : d.Valid) (p : u.Visual) :
    HasSum (fun i => u.price D i V p) (u.sumValue V p) := by
  obtain ⟨a,e,s,hx,w,H⟩ := hv.lawful
  unfold sumValue
  exact HasSum.sum (tallies ..) (HasSum.sum (hasSum_fintype _) (HasSum.sum (balanced u D V h) (HasSum.sum (rectifies u D V h _)
    (HasSum.sum (u.base_sum hv _ _) ((Activities.ESeries H.labels |>.summable (u.hard V p)).hasSum.neg)))))

/-- Canvas for one incoming K-list; no log price on mismatched or
incompatible sectors. -/
def canvas (b : Finset ℕ) (V : Config G c) (p : u.Visual) :=
    if u.Flags V ∧ d.Nonoverlap b then (∏ i, u.gate b i V p)*Real.exp (u.sumValue V p) else 0


end Spot
end YM.AnalyticBridge.LocalGaussian
