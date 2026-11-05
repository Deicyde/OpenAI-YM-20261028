import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.BOUNDARY.Coordinates
import YM.Next.EXTRACTION.Coordinates
import YM.Next.SCHEDULE.Blocks
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Quotient
import YM.Push.PRICE_COMPILER.Suppression

/-!
# Campaign option: SizeBill from finite equation inputs

Uses `Base.null` and the both-stage rank transfer at `Projected` (can be
read even at this f with the reliable-rank estimate only frequently on
fused tails, without need for orientations or transport of the estimate).
For actual later jointly-persistent purchasing request the displayed
per-degree supplies on inherited orders; NOT claiming to pay the physical
Compares estimates or RFree residuals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Grade
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Spec Lattice Wilson Cells
  Next.Extract Next.UVStress Push.Common Snap Push.CutoffProjectors Dash
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f g : Extraction.Order} {w : Snap C} {u : Upper w}

/-- Rank only, may be used even whenever this invoice happens to hold
frequently at a Risen (or on a refinement of it). Needs CUTOFF_PROJECTORS's
actual presentation (kernel statement), residual premise on actual free
coordinates (compare with quotient lemma there). Not spectral leftovers at the
wrong scale. -/
theorem upper_dim (A : Campaign C) (p : Risen u A.presentation f) (d : ℕ) (hr : Maxwell.residual G d = ⊥)
    (hA : ∃ᶠ i : ℕ × ℕ in f.fuse, Injective (A.packet d i.1 i.2).reference) :
    Module.finrank ℂ (u.T.Field d) = Module.finrank ℂ ((Bel C.book).Field d) := by
  let n := Module.finrank ℂ (Maxwell.equationIdeal G d)
  obtain ⟨he,hv⟩ := p.projections.ranks d
  have ht : ∀ᶠ i : ℕ×ℕ in f.fuse,
      Module.finrank ℂ (LinearMap.ker (A.presentation.step d i).toLinearMap)=
        Module.finrank ℂ (LinearMap.ker (w.R d).trueP.toLinearMap) := by
    rw [Extraction.Order.fused]; unfold Extraction.Order.late
    filter_upwards [hv] with i hi
    filter_upwards [he (f.per i)] with j hj
    exact hj.trans hi
  obtain ⟨i,hi,hK⟩ := (hA.and_eventually ht).exists
  have h : Module.finrank ℂ (u.T.null d) = n := by
    rw [p.base.null, ← hK]; rw [A.ker d i.1 i.2]
    exact (LinearMap.finrank_range_of_inj (f := (A.packet d i.1 i.2).reference.toLinearMap) hi).trans (equation_dim _)
  let B := Bel C.book
  have hh : Module.finrank ℂ (B.null d) = n := by
    change Module.finrank ℂ ((Maxwell.freeTable C.book.grid).null d)=_
    rw [← free_null d hr]; exact equation_dim _
  have hp := Submodule.finrank_quotient_add_finrank (u.T.null d)
  have hx := Submodule.finrank_quotient_add_finrank (B.null d)
  rw [h] at hp; rw [hh] at hx
  exact Nat.add_right_cancel (hp.trans hx.symm)

/-- Can provide even at any stage BEFORE this RBase invocation. No
further Deliveries needed unless wanting H/real equivariance of cutoff
projectors or other optional receipts. -/
def Cardinal (A : Campaign C) (F : Extraction.Order) := ∀ d : ℕ, F.late fun N p => Injective (A.packet d N p).reference

lemma Cardinal.persists {A : Campaign C} (p : Cardinal A f) (h : Tails g f) : Cardinal A g := fun d => h.late (p d)
lemma Cardinal.comparison (A : Campaign C) (h : Cardinal A f) (p : Risen u A.presentation f) (r : ∀ d, Maxwell.residual G d=⊥) :
    DimAbove u.T := fun d => (upper_dim A p d (r d) ((show ∀ᶠ i : ℕ×ℕ in f.fuse, Injective (A.packet d i.1 i.2).reference from h d).frequently)).le
end YM.UVNext.Grade
