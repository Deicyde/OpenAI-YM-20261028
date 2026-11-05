import YM.Extra.WILSON_STARTUP.Cake
import YM.Progress.DIRECTED_RECIPE.Bands
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.JOINT_CALENDAR.Issue

set_option warningAsError false

/-!
# A single physical top layout on DirectedRecipe.recipe

Don't compare two recipes selected existentially from `compatible` & `engage`.
We choose the final one *as* the DirectedRecipe Alloy. Surface is
WilsonStartup's Padded dictionary and payload, issued onto the folio (before
any trajectories), as appropriate here. Marker clients must know actual
layout not `Start.layout`: see `portrait`, `traces` and `useOrigins`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.Port
open Function Filter Set Lattice RG RG.Supply RG.Shoot Wilson Input Precision Source
open Next.Scheduling WilsonStartup Ovens Ovens.Pipes Progress.DirectedRecipe
open MeasureTheory
open scoped Matrix.Norms.Frobenius Topology ENNReal

variable {G : Gauge} (a : Levels G)

def pot (N p : ℕ) := Start.dictionary G (a.S.side N p)
def kettle (N p : ℕ) := Start.payload (a.params N).clip (a.budget N) G (a.S.side N p)



/-- The actual recipe filters. Strengthen `first` (and top retain) via the
Permissions on pre-merge Drows, not a test post hoc that could be incompatible
with replays. Continuation predicates incl real splitting, normalization,
fixed addresses and PeriodFuture all still in DirectedRecipe.recipe; any
*additional* continuation requirements supplied here must still be paid by
actual estimates in advancers. Only their follows used. -/
def stamped (further : Permissions a) : Permissions a :=
    { further with starts N p β X d := X=pot a N p ∧ d=kettle a N p β }

variable {a} {O : ChartRatio G} {H : Horizon a} {k : Kin H O}

abbrev AtTop (k : Kin H O) := ∀ N, k.path N N=Design.top G (a.params N).clip

section startup
open WilsonStartup.Start
variable {N p : ℕ}

/-- Issue the SurfacePay & full Curve on actual fields (not a startup invoice
left as a hypothesis). Applies even if there's no blocking at this depth.
-/
lemma card (h : Allows a N) (further : Permissions a) (hk : AtTop k) : Menu k (stamped a further) N p (pot a N p) (kettle a N p) := by
  let b := a.budget N
  let X := band a N
  let c := (a.params N).clip
  obtain ⟨σ,κ,γ,hL,hP⟩ := h.receipt
  have ht : b.threshold ≤ threshold G b.order b.power := h.radius
  have hX (x) (hx : x∈X) : a.clock.hatBeta N/2 ≤ x := hx.1
  have hn x (hx : x∈X) := hL.slope.trans (hX x hx)
  refine ⟨fun β hx => ⟨?_,?_,rfl,rfl⟩, ?_, posed h.clip.direct hn, hL.little h.clip X hX⟩
  · refine ⟨κ,Real.exp γ - 1, Real.exp γ - 1, digests h.clip ht hL (hX β hx) ?_, hL.buys h.clip (hX β hx), hP⟩
    refine le_trans ?_ h.income
    unfold Start.book overhead
    have h₁ := item_pos G (a.budget N)
    have ht : ‖β‖ ≤ 2*a.clock.hatBeta N := by rw [Real.norm_of_nonneg (hn β hx)]; exact hx.2
    gcongr
  · intro U
    rw [hk]
    simp only [kettle,payload,Pi.zero_apply,tsum_zero,Real.exp_zero,mul_one]
    exact evaluates h.clip U
  rw [hk]; exact curve ht h.clip.direct hn



-- Embeddings fixed even through the closed β band.








end startup

section retention
variable {e : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage}
variable {further : Permissions a} {N p : ℕ} {u : Rep G (a.S.side N p)}



-- Also know same top from pointwise (not just on selected trajectories)

end retention

section address
open WilsonStartup.Start Progress.DirectedRecipe.Rack
variable {n : Side}



end address
end YM.Planned.Port
