import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Marginal
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.SectorTags
import YM.MultiNext.VACUUM_STABILITY.Holding.Offers
import YM.Next.SCHEDULE.Blocks
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.PRICE_COMPILER.Suppression
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Change
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen


/-!
# Intact tagged sector integrals with arbitrary complex multipliers

Positive Haar links (auxiliary ones outside Frozen ignored in the
untouched integrand), ONE forest and choice and Allocation,
coarse V, C=fog and meanLog even with repeated source kicks, all full
masks/plaquette rows/predictor tests at actual coordinates in each
section. Wrong output table allowed (zero by the bill). At use take
`g = F.peelRow Q` including the powers and flags on the actual paths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction
open Function Filter Finset Matrix Lattice RG Wilson Precision Multi.Vacuum Next.SectorChange
open MeasureTheory Gaussian Gauss Pressure Bid Tree YM.Push.SectorMeasure YM.Push.LogIdentity
open scoped Topology BigOperators Classical MatrixOrder Tags
variable {G : Gauge} {n f : Side} {S : StepData n f}

/-- Everything shared across all the input literals. Auxiliary post-change
expansion (to relinquish defaults and integrate components) must be of THIS
integrand at every literal, not extrapolated from the integral of the
unmarked density. In particular if using separate branch prescriptions
must implement them via address alternatives in a census.
-/
structure Setting (G : Gauge) (S : StepData n f) where
  tube : Tube G S
  tree : Forest S.ratio
  x : ℝ
  W : ℝ
  cuts : Allocation G S x W
  J : ChartRatio G
  chi : Chi
  d : ℝ

namespace Setting
variable (t : Setting G S)

abbrev Stage := Tags.World G S t.tree
abbrev line (A : Stores S) := Rows.In t.x A t.tree (G:=G)

def plan := Measure.pi (Tags.draw G S t.tree)
instance : IsProbabilityMeasure t.plan := by unfold plan; infer_instance

def outcome (θ : t.Stage) : S.Choices := (Tags.sample G S t.tree θ).2


def mat (A : Stores S) (V : Config G n) (θ : t.Stage) : Gaussian.Table (t.line A) := fog A t.tree t.tube t.x V (t.outcome θ)



def mean (A : Stores S) (V : Config G n) (θ : t.Stage) := meanLog A t.tree t.tube t.x V (t.outcome θ) t.chi t.d ((Tags.sample G S t.tree θ).1 ∘ Subtype.val)

def weight (A : Stores S) (k : S.Choices) (V : Config G n) (β : ℝ) (g : Config G f → ℂ) :=
  regularized t.cuts A t.tree V k t.chi t.J t.d (fun u => S.noise β (S.prediction u k) V • g u)

-- relative to probability (not counting!) on the choice arrays θ.
def untouched (A : Stores S) (V : Config G n) (β : ℝ) (g : Config G f → ℂ) (θ : t.Stage) (z : Vec (t.line A)) :=
  let C := t.mat A V θ
  let r := t.J.scale ^ Fintype.card (Active A t.x t.tree) * chartCost C (coupling β)
  let a := displaced (t.mean A V θ) (coupling β) z
  let Y := (Tags.sample G S t.tree θ).1 ∘ Subtype.val
  ((Fintype.card S.Choices:ℝ)*r*Real.exp (force C z/2)) • t.weight A (t.outcome θ) V β g Y a

def portion (A : Stores S) (V : Config G n) (β : ℝ) (g : Config G f → ℂ) (θ : t.Stage) (z : Vec (t.line A)) :=
  t.untouched A V β g θ (CFC.sqrt (t.mat A V θ) *ᵥ z)

def Matched (A : Stores S) (V : Config G n) := A.flags=RG.flags (temp t.x) V

structure Ready (β : ℝ) : Prop where
  scene : S.patch.Branches S.kernel G
  chart (A V k) : t.Matched A V → Permitted t.x V k A t.tree t.cuts t.J t.d β (fog A t.tree t.tube t.x V k)
      (meanLog A t.tree t.tube t.x V k t.chi t.d)



omit t in
private lemma regularity (k : S.Choices) (V : Config G n) (β : ℝ) {g : Config G f → ℂ} (hg : Envelope g) (hS : S.patch.Branches S.kernel G) :
    Envelope (fun u => S.noise β (S.prediction u k) V • g u) := Env.scale (env_noise S β (S.prediction_meas hS k) measurable_const) hg

omit t in
private lemma push_root {ι : Type} [Fintype ι] [DecidableEq ι] (C : Gaussian.Table (ι × G.ColorIndex))
    (hc : C.PosDef) (m : Prices G ι) (f : LogArray G ι → ℂ) (hm : Measurable f) (b s p : ℝ) (hb : 0<b) :
    (∫ z : Prices G ι, (s * (p * chartCost C b) * Real.exp (force C (CFC.sqrt C *ᵥ z) / 2)) • f (displaced m b (CFC.sqrt C *ᵥ z)) ∂standard _)=
      s • (p • ∫ a,f a) := by
  have hh := (at_price C hc hb m f).2
  let v z := Real.exp (force C z / 2) • f (displaced m b z)
  have hw : Measurable v := by
    have hz : Measurable (fun z => m+b • z) := by fun_prop
    have he : Measurable (fun z => Real.exp (force C z / 2)) := by unfold force mulVec dotProduct; fun_prop
    exact he.smul (hm.comp (tape.measurable.comp hz))
  have ht : (∫ z,v (CFC.sqrt C *ᵥ z) ∂standard _) = ∫ z,v z ∂cloud C := by
    change (∫ z,v (CFC.sqrt C *ᵥ z) ∂coins _) = _; rw [← paid C, integral_map (acts_meas _).aemeasurable hw.aestronglyMeasurable]
  simp_rw [mul_smul]; change _ = _; rw [integral_smul, integral_smul, integral_smul, ht, hh]









end Setting
end YM.ProofPorts.CommonComplexProduction
