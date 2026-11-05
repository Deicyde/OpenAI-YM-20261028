import YM.Next.EXTRACTION.Base
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Fringe
import YM.Push.CUTOFF_PROJECTORS.Passage

/-!
# Consume on one common refinement

Conditional RBin/RBase comparison for this part of the work. The finite
maps remove the image of the **equation cylinders' x matrices**, in
reference coordinates, cutoff by cutoff. It takes much more to talk about
the null space `T.null d` of the normalized YM limits. Here are passages
with actual hypotheses at this frontier. Use the existing heavy
EXTRACTION / CUTOFF_PROJECTORS results with the covariance derived above.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Extraction Dash Next.Extract Push.CutoffProjectors
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {A : Campaign C} {f : Order}

/-- An operational gate (`LocalPrice` suffices; `relax` if given Customs) (use on ordered tails); does NOT include any
matrix-covariance assumptions. c can be purchased via `spectral_bank`
under its exact *other* finite-test & transfer assumptions. Here price
positive in `Separation`'s requested norm with terminal inverse, uniform at
a weight d on this gate. Even in rank-zero case.
-/
def Operational (A : Campaign C) (d : ℕ) (c : ℝ) (N p : ℕ) : Prop :=
  let E := A.packet d N p
  LocalPrice E ∧ E.Separation c



/-- The stronger *each fixed p* gate used when identifying even the
inner limit's representation, not automatic just because the projections
converged in extraction. -/
def Served (A : Campaign C) (d : ℕ) (f : Order) (c : ℝ) :=
  ∀ p : ℕ, ∀ᶠ j : ℕ in atTop, Operational A d c (f.mesh j) p



lemma Served.refine {d : ℕ} {c : ℝ} (h : Served A d f c) (g : Order) : Served A d (f.refine g) c :=
  fun p => g.mesh.cofinal.eventually (h p)



/-- Output package. `S` raw, `M` period tables, `T` smooth table on the same
ordered extraction as `R`, no additional subsequences in the kernel or
quotient comparison. Conditional statements in the record describe the use
if given the corresponding *additional* physical data. -/
structure Retains (A : Campaign C) (f : Order) (S : Table C.book) (M : ℕ → Table C.book) (R : Bin S)
    (z : (d : ℕ) → ℕ → CoordMap C d) (T : Table C.book) (W : DiffPlan T) : Prop where
  maps : Projected A.presentation f R z
  builds : Base C f S M R T W
  identity (d : ℕ) :
    (R d).trueP = retain (C.labels.level d) (T.null d) ∧ Aligned (C.labels.level d) (T.null d)
  limit (d : ℕ) : Commuting (C.labels.level d) (R d).trueP
  inner (d : ℕ) (c : ℝ) : Served A d f c →
    ∀ p : ℕ, Commuting (C.labels.level d) (z d p) ∧ Aligned (C.labels.level d) (lost _ (z d p))

namespace Retains
variable {S : Table C.book} {M : ℕ → Table C.book} {R : Bin S} {z : (d : ℕ) → ℕ → CoordMap C d}
    {T : Table C.book} {W : DiffPlan T}






end Retains




end YM.ProjectorNext.Equivariance
