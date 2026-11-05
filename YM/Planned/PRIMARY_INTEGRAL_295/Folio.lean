import YM.Planned.PRIMARY_INTEGRAL_295.Warehouse

/-!
# Finite pre-L branch of the B70 price book

Actual primary analytic + matrix assumptions across all admitted
pre-index cases. No stage-precedence claim using drift; use Fits' stated
J fork (including equality). This builds an order table for ALL before
length choices. Does not verify that choices Ink/Stage suffice for
station/kernel. Use with Doors on same schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Folio
open Function Filter Set Lattice Labels Source RG Wilson Next.Foundations Extra.Histories Bid Warehouse
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d j t : ℕ}

-- phase envelope maxima. Each tuple precomputed (includes
-- small-hull geometry for canonical columns). `indices j t` means actual
-- tuning when clockwise j, prev clock t<=j.
abbrev Library := ℕ → ℕ → ℕ → Ink

structure Okay (g : ℕ→Stage) (j t d : ℕ) : Prop where
  fine : 4≤j
  coarse : 4≤t
  fork : t≤j ∧ j≤t+1
  cover : d+3 ≤ t
  work : d≤(g t).order
  proof : d≤(g t).power

def shoes (G : Gauge) (u : Library) {g : ℕ→ Stage} (h : Okay g j t d) : Supplies j t d where
  ink := u j t d
  order := (g t).order
  power := (g t).power
  exponent := (g t).supportExponent
  credit := Next.Foundations.price G (max (g t).order (g t).power)
  fine := h.fine
  coarse := h.coarse
  fits := h.work
  run := h.proof
  flat := by obtain ⟨_,_,⟨a,_⟩,hx,_⟩:=h; omega
  nonneg := zero_le_one.trans (Next.Foundations.price_one_le ..)

def Buy (G : Gauge) (u : Library) (K : KernelChoices) (g : ℕ → Stage) (C : ℕ → ℝ) : Prop :=
    ∀ j t d, ∀ h : Okay g j t d, outlay (localSection G d) (sound G d) (valuation G d) (shoes G u h) K ≤ C j




end YM.Planned.PrimaryIntegral295.Folio
