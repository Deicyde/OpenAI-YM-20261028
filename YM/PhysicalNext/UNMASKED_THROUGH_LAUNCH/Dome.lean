import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Extra.MULTISOURCE_BOUNDS.Schedule
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.Extra.SOURCE_HISTORIES.Accompany
import YM.Extra.SOURCE_HISTORIES.Reserve
import YM.Extra.WEAK_SCALING_ACTLAW.Divergence
import YM.Extra.WEAK_SCALING_ACTLAW.Five
import YM.Extra.WILSON_STARTUP.Clock
import YM.Extra.WILSON_STARTUP.Match
import YM.Next.MAXWELL.Det
import YM.Next.MULTISOURCE.Curves
import YM.Next.STATIONARY.Level.Recurse
import YM.Next.STATIONARY.OneLoop.Bubbles
import YM.Next.UV_STRESS.Annulus
import YM.Next.UV_STRESS.Birth
import YM.Next.WARD_BIN.Eqs
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.Progress.JOINT_CALENDAR.Issue
import YM.Progress.STATIONARY_SCENES.Frames
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Passage
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.BETA_TRANSPORT.Margins
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.LOCAL_SPLITTING.Clocks
import YM.Push.PRICE_COMPILER.Suppression
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.RELAY_MARK.Span
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.Push.STRESS_FLUX.Low



/-!
# Coupling `Next.STATIONARY` to free-kernel purchase and `Builder`

Utilities for choosing the parameters. Preserve clip across the analytic pre-L
calculations. Cf. `B70FreeStationaryConnection`; here need to keep the theorem
across changes to floorL and through `Builder`'s changes to the Horizon. This
path goes up to Directed and genuine cutoff launches, not Program. See Merchant
for pricing order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.ThroughLaunch
open Function Filter Lattice RG Source Wilson Precision RG.Supply
open WilsonStartup  Extra.Histories Next.Foundations
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

/-- Stage orders/support exponents. Choose monotone stage asks before applying. -/
structure Orders where
  first : ℕ
  jets : ℕ → ℕ
  position : ℕ → ℕ
  supportExp : ℕ → ℝ

structure Draft (p : Orders) : Prop where
  cut : 4 ≤ p.first
  mono : Monotone p.jets
  mono2 : Monotone p.position
  ascend : Monotone p.supportExp
  positive i : 0 < p.supportExp i
  k i : max 6 i ≤ p.jets i
  heights i : max 2 i ≤ p.position i

/-- Reanchor tests require keeping the orders in these very frames (not only
some tendsto infinity guarantee). -/
structure WithStage (s : Sheet G) (p : Orders) : Prop where
  first : s.first=p.first
  jets i : (s.profile i).order=p.jets i
  powers i : (s.profile i).power=p.position i
  prices i : (s.profile i).supportExponent=p.supportExp i

/-- Actually small direct Clip per j, window relaxation can grow according to
RLoops's chosen width. Need later
expenses independently justified. -/
lemma housing {K : KernelChoices} (hk : ∀ P : Patch,P.Branches K G)
    {p : Orders} (hd : Draft p) (b : ℕ → ℕ) (g w : ℕ → ℝ) (hg : ∀ i, 0 < g i)
    (hw : ∀ i, 0 < w i) : ∃ s : Sheet G, s.kernel=K ∧ s.floorL=b ∧ WithStage s p ∧
      ∀ i : ℕ, (s.profile i).clip.direct ≤ g i ∧ (s.profile i).clip.direct ≤ 1 ∧ (s.profile i).width = w i := by
  let q i := min (g i) 1
  have ho i : 0 < q i := lt_min (hg _) zero_lt_one
  let c (i : ℕ) : Clip := ⟨q i,q i/32,12/(w i),ho i,by positivity [ho i],by linarith [ho i],by positivity [hw i]⟩
  let t (i : ℕ) : Stage := ⟨c i, p.jets i,p.position i,p.supportExp i,w i, 1,0,1,(le_max_left ..).trans (hd.k i),
    (le_max_left ..).trans (hd.heights i),hd.positive i,hw i,one_pos,
    (div_le_iff₀ (hw i)).mp le_rfl,le_rfl,le_rfl⟩
  let s : Sheet G := ⟨K,hk,t,p.first,hd.cut,hd.mono,hd.mono2,hd.ascend,b⟩
  exact ⟨s,rfl,rfl,⟨rfl,fun _=>rfl,fun _=>rfl,fun _=>rfl⟩,fun i => ⟨min_le_left ..,min_le_right ..,rfl⟩⟩

/-- Needed after choosing both prices and clip. Preserve width and order/support
slots through last pre-knobs here. -/
lemma developer {g : ℕ → ℝ} {K : KernelChoices} (s : Sheet G) (hk : s.kernel=K)
    (hc : ∀ i ≥ s.first,Design.Suitable G (s.profile i)) (hg : ∀ i,(s.profile i).clip.direct≤g i)
    {p : Orders} (hp : WithStage s p) (h : Draft p) (u : ℕ → ℕ) (d : ℕ → ℝ)
    (C : ℕ → ℝ) (hC : ∀ i,1 ≤ C i) : ∃ s' : Sheet G,∃ M : Bid.Worth,
      s'.kernel=K ∧ WithStage s' p ∧ Doors.Plans s' C M ∧ s.floorL ≤ s'.floorL ∧
      Stationary.Buys s' (fun i => (s.profile i).width) (fun i => (s.profile i).paths) d u g ∧
      (∀ i,((s'.profile i).order.factorial:ℝ) ≤ (s'.profile i).columns) ∧
      ∀ i,s'.first ≤ i → Design.Suitable G (s'.profile i) := by
  let f (i) : Stage := {s.profile i with
    drift:=max (s.profile i).drift (d i),
    drift_ge:=(s.profile i).drift_ge.trans (le_max_left ..)}
  let t : Sheet G := Extra.Multi.buyFactorial {s with profile:=f,floorL:=fun i => max (s.floorL i) (u i)}
  obtain ⟨ℓ,S,hk',hF,hQ,hL,h',W,hP⟩ := Doors.alone t C hC (fun j => And.intro
    (show j ≤ (t.profile j).order from (hp.jets _).symm ▸ (le_max_right ..).trans (h.k _))
    (show j ≤ (t.profile j).power from (hp.powers _).symm ▸ (le_max_right ..).trans (h.heights _)))
  -- transport lemma for THIS final S. equalities below avoid re-evaluation of Ω after L-boost.
  have he Z (z : ℕ) (f : Stage→Z) (h : ∀ (a b : Stage), f ({ a with columns := b.columns, columns_ge := b.columns_ge } : Stage) = f a) :
      f (S.profile z) = f (t.profile z) := by
    rw [congr_fun hL z]; calc
      _ = _ := congr_arg f (h' z).2
      _ = _ := h _ _
  have hh i := he ℕ i Stage.order (fun _ _ => rfl)
  have hz i := he Clip i Stage.clip (fun _ _=>rfl); have hi i := he ℝ i Stage.width (fun _ _=>rfl)
  have hu i := he ℝ i Stage.paths (fun _ _=>rfl)
  refine ⟨S,W,hk'.trans hk, ⟨hQ.trans hp.first,fun i => (hh i).trans (hp.jets _),fun i =>
    (he _ i Stage.power (fun _ _=>rfl)).trans (hp.powers _),fun i => (he _ i Stage.supportExponent
      (fun _ _=>rfl)).trans (hp.prices _)⟩,hP, fun i => ?_, ⟨fun i => by rw [hz i]; exact hg i,fun i => ⟨hi i,hu i⟩,
        fun i => (he _ i Stage.drift (fun _ _=>rfl)).symm ▸ le_max_right .., fun i => by rw [hF]; exact le_max_right ..⟩, ?_,?_⟩
  · rw [hF]; exact le_max_left ..
  · intro i; rw [hh,congr_fun hL]
    exact le_trans (Extra.Multi.bought _ _) (h' i).1
  intro i hI
  refine ⟨(congrArg Clip.direct (hz i)).symm ▸ (hc i (hQ ▸ hI)).direct, ?_⟩
  rw [hz,hi,hu]; exact (hc i (hQ ▸ hI)).paths
end YM.PhysicalNext.ThroughLaunch
