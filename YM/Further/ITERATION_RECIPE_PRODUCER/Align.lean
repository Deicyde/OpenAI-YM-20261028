import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.ITERATION_NO_LOSS.Roots
import YM.Extra.WILSON_STARTUP.Clock
import YM.Extra.WILSON_STARTUP.Overlay
import YM.Progress.JOINT_CALENDAR.Kinetics


set_option warningAsError false

/-!
# Actual common metric, harmonic and period handoff

Use the positive choice through the modified top as in
`WilsonStartup.Change`, BEFORE Kin; thus even at the exceptional first step
**all towers** are the same. Top metric replaced on general two-forms,
not asserted unchanged except after applying to d₁; the two unmodified
H/H^{-1} rows at all signed translations and their inherited curvature
columns are the same on the cover. Costs pre-L. Harmonic here is the one
needed on T for `ITERATION_NO_LOSS`, not a property of any preselected loop.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Further.IterationRecipe
open Filter Function Matrix Lattice Laurent Bloch Precision RG RG.Supply Exterior Bid Craft
open Next.Free Next.Scheduling Progress.Joint WilsonStartup Change Design
open Extra.Iteration hiding Aligned
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {j t : ℕ} {K : MapPrices} {a : Levels G}







/-- More alignment than mere `Harmonic`. Exact normal orientation A0,T &
root choices and all-period comparisons before any shrinking/extraction.
`H` is the horizon to use; keep the pinning witnesses for further proof
work. Does NOT require `Craft.Rack a X H` or `Free.Present a H l` (the
modified metric and Bleeps are not assumed at the local replacement).
-/
structure Panel (K X : MapPrices) (l : ℕ → ℝ) (H : Horizon a) : Prop where
  covers : H.Suffices K
  oath : Swears H
  symmetric N m (n : Side) : m ≤ N → ((H.H N m).roots.acts n).PosDef
  ancestry : ∃ M B : Horizon a, Craft.Rack a X M ∧ Retained B M ∧ B.Suffices K ∧ Present a B l ∧ H = mapped B

variable {X : MapPrices} {H : Horizon a} {l : ℕ → ℝ} (hp : Panel K X l H)
namespace Panel
include hp
lemma peak N : H.H N N = bed (a.params N).clip := by obtain ⟨M,B,_,_,_,_,rfl⟩ := hp.ancestry; exact (overlaid _).peak N





end Panel


end YM.Further.IterationRecipe
