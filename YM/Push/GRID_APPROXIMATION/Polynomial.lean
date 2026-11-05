import YM.Next.BOUNDARY.Alias
import YM.Next.FOUNDATIONS.SU2
import YM.Push.GRID_APPROXIMATION.Picture

/-!
# Use also on ordinary separated cluster polynomials

A stronger comparison available on ordered tails. Fixed data still independent
of N,p. The separation bound here is periodic in native h-grid steps. Does
not require genericity across DIFFERENT terms of the polynomial. Supports in
the same shrinking clouds from `planted_outputs`. This extension (additional
 use) does not create fields on coincident positions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox.Polynomial
open RG Lattice Wilson MeasureTheory Function Filter Set Cells OS
open scoped Topology BigOperators

variable {G : Gauge} {ι : Type*} [Fintype ι]

structure Model (C : Family G) (ι : Type*) (h : ℕ) where
  n : ι → ℕ
  labels (i : ι) : Fin (n i) → C.book.Token
  q : ι → ℝ
  x (i : ι) : Fin (n i) → Cover
  apart i : Injective (x i)
  cards (i j) : Figures C (labels i j) h

variable {C : Family G} {h : ℕ} (M : Model C ι h)









-- A loose periodic separation threshold (native h-grid steps).
def size := Finset.univ.sup fun i => Finset.univ.sup fun j => Finset.univ.sup fun p : Axis => (M.x i j p).natAbs







variable {f : Extraction.Order} (he : ∀ i j,(M.cards i j).Gives f)
include he






end YM.Push.GridApprox.Polynomial
