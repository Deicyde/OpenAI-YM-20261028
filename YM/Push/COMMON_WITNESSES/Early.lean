import YM.Next.EXTRACTION.Basis
import YM.Push.COMMON_WITNESSES.Link


/-!
# Use on an earlier extraction

Can even split up Center and projection affordability under successive
station receipts. Include a real consumer of the study-based version and
those. Physical choices still BEFORE all extractions (incl parameter
pricing of schedule); not proclaiming the history or comparison
estimates. Pin every invocation and final table to C. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set Extraction Cells Table Next.Extract Spec Org Snap
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {b : Presentation C} {f : Order}
variable {ι : ℕ → Type*} [∀ d, Fintype (ι d)]

/-- Precision in exponent uses toll j decreasing to zero. Power constants
(independent m) bought before splitting bills. Fixed-period budgets only
on the row, no p uniformity there. -/
structure EarlyCosts (C : Family G) where
  wait : ℕ → ℕ → ℕ         -- d p at per budget
  pause : ℕ → ℕ → ℕ        -- d and j at power
  refpaid d j : C.ref d≤pause d j
  power : ℕ → ℕ → ℝ
  positive d j : 0 ≤ power d j

abbrev Before := (ℕ × Option ℕ) ⊕ (ℕ × (ℕ × ℕ × Option ℕ))

variable (B : ∀ d, Module.Basis (ι d) ℂ (C.label d)) (K : EarlyCosts C)

def launchBill (b : Presentation C) : Before → Order → Prop
  | .inl (d,none),f => ∃ D : ℝ, 0≤D ∧ f.late fun N p => ‖b.step d (N,p)‖ ≤ D
  | .inl (d,some p),f => ∃ D : ℝ, 0≤D ∧ ∀ᶠ j in atTop, ‖b.step d (f.mesh j,p)‖ ≤ D
  | .inr (d,m,p,none),f => K.wait d p≤m → ∃ D : ℝ, 0≤D ∧ ∀ᶠ j in atTop, ∀ i,
      centeredBudget C ⟨d,B d i⟩ D m (f.mesh j) p
  | .inr (d,m,j,some l),f => K.pause d j≤m → f.late fun N p => ∀ i, centeredBudget C ⟨d,B d i⟩
      (K.power d j * (C.S.a m)^(-(d:ℝ)-toll j)+toll l) m N p

omit [∀ d, Fintype (ι d)] in
lemma launch_upon (r : Before) (h : launchBill B K b r f) {g : Order} (he : Tails g f) : launchBill B K b r g := by
  rcases r with (⟨d,_|p⟩|⟨d,m,p,_|l⟩)
  · obtain ⟨D,hD,H⟩ := h; exact ⟨D,hD,he.late H⟩
  · obtain ⟨D,hD,H⟩ := h; exact ⟨D,hD,he.mesh.holds (fun N => ‖b.step d (N,p)‖ ≤ D) H⟩
  · intro H; obtain ⟨D,hD,H⟩ := h H; exact ⟨D,hD,he.mesh.holds (fun N => ∀ i, centeredBudget C ⟨d,B d i⟩ D m N p) H⟩
  intro H; exact he.late (h H)




end YM.Push.Common
