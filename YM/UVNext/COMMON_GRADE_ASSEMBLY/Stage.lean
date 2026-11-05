import YM.UVNext.COMMON_GRADE_ASSEMBLY.Approach
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Charges
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free

/-! # From first Hosted order to actual Playing on a common inherited order

Versions also before Hosted and RBase, see `blueprint`, `Campaign.lean`.
Only Station and Leg receipts, no `Probed` universal,
no uniform choice of radii across different Ward basis observables, no
`Climb.Track` prerequisites, and no change AT ALL in the Lab (table S)
and its plan/phase costs to obtain these UV proofs. Keep even the specific
Holder & all ranks/detector/raw and quantitative grille from Hosted. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Grade
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Spec Lattice Wilson Cells
  Next.Extract Next.UVStress Push.Common Snap
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f g : Extraction.Order} {w : Snap C} {u : Upper w} {b : Presentation C}
variable {Q : Guests u.T} {W : MaxwellData C} {I : IR (C:=C) u.T}





/-- Versions with persistent stock suppliers. A convenience predicate for a
campaign to pay at this point, while allowing its choices/needs to depend on
prior production; the free comparator is one fixed W per Grades job. The
f argument is used to say only at Hosted on orders below f. Isn't itself
`∃ ... Playing` or assumption of existence of grades.
-/
def AfterHost (u : Upper w) (b : Presentation C) (f : Extraction.Order) : Prop :=
  ∀ g (Q : Guests u.T) (p : Hosted u b Q (f.refine g)), ∃ a : FreeInput C,
    a.Divergence ∧ WeakStock C a.kernels.spin (f.refine g) ∧
    ∀ j, Stations C ((f.refine g).refine j) a.kernels.spin →
      (∃ J : u.T.Stress, J ∈ KernelSpace p.seed.kernel.spin ∧ J≠0 ∧ Conserved u.V p.seed.kernel.spin J) →
      ProbeOffer ((f.refine g).refine j) p.seed.kernel u.V

/-- Stronger persistent supplies (need if choosing before the stock invoices
are due); compatible with *all* orders below f. Same free comparator as well.
At RBase can be on the actual Kernel already. Avoid predetermining stress
sign/axis over the field locations, even here. -/
structure Descendants (u : Upper w) (a : FreeInput C) (F : Extraction.Order) (H : u.T.Hierarchy) : Prop where
  drift : OnDemand F (WeakBill C a.kernels.spin)
  labor : (∃ J : u.T.Stress,J∈KernelSpace H.spin ∧ J≠0 ∧ Conserved u.V H.spin J) → ProbeDemand F H u.V



lemma posts (a : FreeInput C) (h : a.Divergence) (H : u.T.Hierarchy) (p : Descendants u a f H) (b : Presentation C) :
    AfterHost u b f := by
  intro g Y hY
  have hp := Tails.refine f g
  refine ⟨a,h,OnDemand.stations (demand_persists p.drift hp), fun _ _ s =>
    ((p.labor s).persists ((Tails.refine _ _).trans hp)).offers⟩









end YM.UVNext.Grade
