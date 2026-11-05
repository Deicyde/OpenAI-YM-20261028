import YM.Push.SECTOR_MEASURE.Decompose

/-!
# The grant through the intact sector partition 

Buys the earned exponential once per A. Same κ across the *whole*
partition (and even across W's delay range in x for a fixed large W).
Allows spending on any subcollections still carrying the prerequisites
(here by integrable multipliers, even ones depending on A at an
individual column); not assuming dropped defaults preserve the estimate.
NO bound here on the magnitudes of remainders in successive RG steps.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure

open Filter Function Lattice RG Wilson Pressure Pressure.Stores Tree MeasureTheory
open Next.Fluctuations.Sector
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
  {x W κ : ℝ}

/-- Kernel Haar prefactor times the assigned seed exponential.
Every coefficient relative to probability Haar, no bare/partition
normalization included in this cost. -/
def earn (S : StepData c f) (G : Gauge) (x κ β : ℝ) (m : ℕ) : ℝ :=
  prefactor S G β * Real.exp (-β*(κ*(fiery G x S.patch.L)^2*m))

theorem earn_pos (S : StepData c f) (G : Gauge) (x κ β : ℝ) (m : ℕ) : 0 < earn S G x κ β m :=
  mul_pos (prefactor_pos β) (Real.exp_pos _)

def Charged (T : Tube G S) (x W κ : ℝ) :=
  ∀ (D : Allocation G S x W) (A : Stores S) (F : Forest S.ratio) (β : ℝ), 0 ≤ β →
    ∀ (V : Config G c) (g : S.Choices → F.Slice G → ℝ), (∀ k, Integrable (g k) (F.order G)) →
    (∀ k a, 0 ≤ g k a) →
    D.column A F V (inside F T β x V g) ≤ earn S G x κ β A.shares * D.column A F V (remainder F A T β x V g)

/-- Substitute partition factors as multipliers in a real grant; the
substitution is legitimate for all tags, including ineligible ones. -/
lemma charged_of_plots (hT : P.Funds S T)
    (h : ∀ (A : Stores S) (F : Forest S.ratio) (β : ℝ), 0 ≤ β →
    ∀ (V : Config G c) (g : S.Choices → F.Slice G → ℝ), (∀ k, Integrable (g k) (F.order G)) →
    (∀ k a, 0 ≤ g k a) →
    (∑ k, ∫ a in onSector A F x W k V, g k a * incoming T β x k V (F.drape a) ∂F.order G) ≤
      earn S G x κ β A.shares *
      ∑ k, ∫ a in onSector A F x W k V, g k a * outgoing A T β x k V (F.drape a) ∂F.order G) :
    Charged T x W κ := by
  intro D A F β hl V g hg hz
  have hB := funds_branch hT
  rw [← D.plots_column hB A F V _ (ticket_in F β x V g) (fun k => inside_integrable F β x V g hT k (hg k)),
    ← D.plots_column hB A F V _ (ticket_out F β x V g A) (fun k => remainder_integrable F β x V g hT A k (hg k))]
  have hp k a : 0 ≤ D.portion A F V g k a := mul_nonneg (D.nonneg ..) (hz _ _)
  have hh := h A F β hl V (D.portion A F V g) (fun k => D.portion_integrable hB A F V g k (hg k)) hp
  simpa only [Allocation.portion, inside, remainder, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hh

/-- Use also with committed heights/W (as opposed to the existential
grant), e.g. given the pointwise inequalities of `Testing.notation_ticket`.
Only require through actual Plot points on the actual slice. -/
theorem charged_at (hT : P.Funds S T)
    (h : ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c), ∀ (a : F.Slice G) k,
      a ∈ onSector A F x W k V →
      κ*(fiery G x S.patch.L)^2*A.shares ≤ A.assessed T x (F.drape a) (S.prediction (F.drape a) k) V) :
    Charged T x W κ := charged_of_plots hT fun A F β hl V g hg hz =>
  (peel hT A F x W κ β hl V (h A F V) g hg hz).2











end YM.Push.SectorMeasure
