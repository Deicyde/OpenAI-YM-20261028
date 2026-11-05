import YM.Next.FREE_KERNELS.Train
import YM.Push.PRICE_COMPILER.Post


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Actual costs for path address conventions

Extend Canonical of the price compiler: permit countable splittings over path labels (signed
weights allowed with pre-L budget), and *any* choices, if path length fits on the cover for
each nonzero label. Periodized endpoints still use true cover offset, even on side 1. Useful
for fitting generators that need more reorientation freedom than a single `Canonical.row`.
A proof template along with sufficiency gates at the same price order; only for the ACTUAL
PathData.Bounds interface in B70. Does not ascribe any further symmetry to path conventions;
retain conventions whenever matching higher jets. Section `Layout` even handles the
harmonic metric condition directly from Attached + row l¹, for presentations with a separate
counting argument. (Also see F03/Metric for periodized derivative given the WHOLE Bounds.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Function Lattice RG RG.Supply Wilson Precision Craft Pressure Laurent Exterior Bloch
open Push.PriceCompiler
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge}

abbrev Place := PlaqAxes × Cover

section Layout
variable (W : PathData G)




end Layout

/-- One tie-array convention in a channel. Can choose differently on each invocation.
Length charged at `stride` times offset radius plus `base`. Uniform splitting mass
(set `mass=1` e.g. if nonnegative weights). All three parameters bought independent
of L and earlier blocking depth (see Seats below).
-/
structure Ways (stride base mass : ℝ) where
  charges : PlaqAxes → Place → ℕ → ℝ
  whereTo : PlaqAxes → Place → ℕ → Slot
  stride_nonneg : 0 ≤ stride
  base_nonneg : 0 ≤ base
  mass_pos : 0 < mass
  pays b x : SumBudget (fun i => |charges b x i|) mass
  completes b x : ∑' i, charges b x i = 1
  layout b x i : charges b x i ≠ 0 →
    ((whereTo b x i).plaq,(whereTo b x i).offset) = x
  length_le b x i : charges b x i ≠ 0 →
    ((whereTo b x i).length:ℝ) ≤ stride * size (α:=Axis) x.2 + base

def pathAddresses : ℕ ≃ Place × ℕ := by
  have : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩
  letI : Denumerable (Place × ℕ) := Classical.choice (nonempty_denumerable _)
  exact (Denumerable.eqv _).symm

namespace Ways
variable {s d m : ℝ} (v : Ways s d m)

def row (B : Bed) (b : PlaqAxes) : ℕ → (ℝ × Slot) :=
    (fun i : Place × ℕ => ((v.charges b i.1 i.2) * B.roots (plaquette b) (plaquette i.1.1) i.1.2, v.whereTo b i.1 i.2)) ∘ pathAddresses







end Ways

/-- Row *at b* cost. No G or level-depth dependence hidden. If also taking
FiniteBounds nuts/costs those are separate. -/
def wayPrice (opening base mass A : ℝ) : ℝ := (mass * Real.exp (opening * base)) * ((Fintype.card PlaqAxes:ℝ)*A)







namespace Ways
variable {u d m : ℝ} (v : Ways u d m)


end Ways
end YM.UVNext.PricedKernels
