import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Roster

/-!
# Absolute L¹ recombination for the tail estimate

Reassemble the *field* tests into the integral caller. This is after
issuing a particular marked or unmarked field expansion; such an expansion
must be of the true multiplier (`body`) with no normalized-integral or
cutoff omissions. `∑'` here sorts on a stable label set. For this particular
argument we don't need joint measurability in V. Do not commute an integral
over V with one in z on these proofs alone.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp.Roster
open Filter Function Lattice RG Pressure Wilson Tree MeasureTheory Matrix
open Next.SectorChange Next.SectorChange.Gaussian SectorNext.Vacuum.ReLog
open YM.Push.SectorMeasure Finset Inventory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius YM.Push.SectorMeasure

variable {c f : Side} {G : Gauge} {x W : ℝ} {S : StepData c f}
variable {T : Tube G S} {R : Rep G f} {D : Allocation G S x W} {F : Forest S.ratio}
  {L : Almanac T D R F} {V : Config G c} {E ι : Type} [DecidableEq E] {K : Cards S ι E}
  (H : Roster L V K) (ψ : H.Script)

/-- Alphabet dissection test. No divides by an integral. -/
def noteField (m : Finset E) (Q : Finset ι) (A : Stores S) (k : S.Choices) : Room G x F A → ℝ :=
  if h : A.flags=RG.flags (temp x) V ∧ K.Makes A m Q then H.imprint ψ h.1 h.2 k else 0

def Spells (g : Stores S → ReadAt S G) (m : Finset E) :=
    ∀ (A : Stores S) (k : S.Choices), A.flags=RG.flags (temp x) V →
      ∀ᵐ y ∂L.climate V A k, HasSum (fun Q : Finset ι => H.noteField ψ m Q A k y) (L.body V A k (g A) y)

/-- Intermediate estimate, to be derived using actual costs on the factors. -/
structure LetterBudget (v : ι → ℝ) : Prop where
  index : H.uniform ψ
  nonneg i : 0 ≤ v i
  summable : Summable v
  each i k : Integrable (ψ i k) (H.paper i k)
  bill i k : (∫ z,‖ψ i k z‖ ∂H.paper i k) ≤ v i

variable {H ψ} {A : Stores S} {g : Stores S → ReadAt S G} {m : Finset E} {v : ι → ℝ}









variable [Countable ι]




end YM.AnalyticBridge.Sharp.Roster
