import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import YM.MultiNext.VACUUM_STABILITY.Holding.Offers
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.ROTATIONS.Charge
import YM.Next.ROTATIONS.Pairs
import YM.Next.SCHEDULE.Air
import YM.Next.SCHEDULE.GridCost
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.History
import YM.Push.BETA_TRANSPORT.Margins
import YM.Push.COMMON_WITNESSES.Fields
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.PRICE_COMPILER.Suppression
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian

/-!
# Bath for each complete-support component of a physical word

With a covariance prescription that may vary even in a smooth component.
Must be the marginal of the one run geometry (verification BEFORE splitting
in `Parallel`). Doesn't split REAL hard arguments from actual analytic
arguments at a repeated physical lookup. Need the marginalized
probabilities under the same θ and actual frame rules in assemblies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction
open Function Filter Finset Matrix Lattice RG Wilson Precision Multi.Vacuum Next.SectorChange
open MeasureTheory ProbabilityTheory Gaussian Gauss
open scoped Topology BigOperators Classical MatrixOrder

variable {G : Gauge} {n : Side}

structure Bath (G : Gauge) (n : Side) where
  tag : Type
  axis : Type
  [many : Fintype axis]
  [inspect : DecidableEq axis]
  [ms : MeasurableSpace tag]
  bill : Measure tag
  [one : IsProbabilityMeasure bill]
  cov : Config G n → tag → Gaussian.Table (axis × G.ColorIndex)

attribute [instance] Bath.many Bath.inspect Bath.ms Bath.one

namespace Bath
variable (T : Bath G n) {X : Type} [RCLike X]

abbrev Line := T.axis × G.ColorIndex
abbrev Play := Vec T.Line

def warm (U : Config G n) (θ : T.tag) (z : T.Play) := CFC.sqrt (T.cov U θ) *ᵥ z

def law := T.bill.prod (standard T.Line)
instance : IsProbabilityMeasure T.law := by unfold law; infer_instance

def sectionAt (U : Config G n) (q : T.tag → T.Play → X) (θ : T.tag) := ∫ z, q θ (T.warm U θ z) ∂standard T.Line

def readout (U : Config G n) (q : T.tag → T.Play → X) := ∫ θ,T.sectionAt U q θ ∂T.bill

def mass (U : Config G n) (q : T.tag → T.Play → X) := T.readout U (fun i z => ‖q i z‖)
lemma mass_pos (U : Config G n) (q : T.tag → T.Play → X) : 0≤T.mass U q := integral_nonneg fun _ => integral_nonneg fun _ => norm_nonneg _

structure Usable (U : Config G n) (q : T.tag → T.Play → X) : Prop where
  joint : Measurable (uncurry q)
  int θ : Integrable (fun z => q θ (T.warm U θ z)) (standard _)
  allint : Integrable (fun p : T.tag × T.Play => q p.1 (T.warm U p.1 p.2)) T.law

lemma Usable.weight {U : Config G n} {q : T.tag → T.Play → X} (h : T.Usable U q) : T.Usable U (fun i z => ‖q i z‖) :=
    ⟨h.joint.norm,fun θ => (h.int θ).norm,h.allint.norm⟩


end Bath

variable {α β K : Type} [MeasurableSpace α] [Fintype K] [Fintype β] [DecidableEq β]

/-- Entry agreement on every physical and query argument used in the
standalone evaluations. Not pricing a law obtained from integrating out
some other (e.g., re-sampled on overlapping components) family. Includes
`α` (tags & Haar) with the correct single normalization. Projection at θ
given by matrices (e.g. `pluck`, or selected color rotations). Comparison
of support-dependent tables must hold even as V varies unless invoked only
at `Reads` fields. -/
structure Parallel (T : K → Bath G n) (U : Config G n) (π : Measure α) (C : α → Gaussian.Table β)
    (θ : ∀ i : K, α → (T i).tag) (R : ∀ i : K, α → Matrix ((T i).Line) β ℝ) : Prop where
  sanctioned x : (C x).PosDef
  smooth_meas i j : Measurable (fun x => CFC.sqrt (C x) i j)
  local_law : MeasurePreserving (fun x i => θ i x) π (Measure.pi fun i => (T i).bill)
  reader i j k : Measurable (fun x => R i x j k)
  diagonals x i : (R i x)*(C x)*(R i x)ᵀ = (T i).cov U (θ i x)
  separate x i j : i≠j → (R i x)*(C x)*(R j x)ᵀ=0

namespace Parallel
variable {T : K → Bath G n} {U : Config G n} {π : Measure α} {C : α → Gaussian.Table β} {θ : ∀ i, α → (T i).tag}
    {R : ∀ i, α → Matrix (T i).Line β ℝ} {X : Type} [RCLike X]






end Parallel
end YM.ProofPorts.CommonComplexProduction
