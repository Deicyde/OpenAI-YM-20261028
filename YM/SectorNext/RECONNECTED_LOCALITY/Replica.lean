import Mathlib.Probability.Distributions.Gaussian.Multivariate

set_option warningAsError false

/-!
# Replica check for the independent reference coordinates (NOT independent likelihoods)

Think one pi law jointly for tree tags if using them,
physical frame-site and coarse-bond outcome tags, and potentially-frozen Y link
values (read only the actual ones).

Integrate Z first **conditional** on these,
so no carrying costs from e.g. multiplying separate estimates for choices which
read a common tag.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
namespace Bind

open Function MeasureTheory Filter
open scoped BigOperators

variable {ι δ : Type*} {Y : ι → Type*} [∀ i,MeasurableSpace (Y i)]

abbrev Tables (Y : ι → Type*) := ∀ i,Y i




variable [Fintype ι] [Fintype δ] (μ : (i : ι) → Measure (Y i)) [∀ i, IsProbabilityMeasure (μ i)]







/-! Parallel statements for Gaussian coordinate reads AFTER verifying a
common-law map on their join, no requirement to apply `replicas` to Z. -/
section pull
variable {J : δ → Type*} {E : Type*} [MeasurableSpace E] [∀ j,MeasurableSpace (J j)]
variable (measure : Measure E) (R : (j : δ) → Measure (J j)) [∀ j,IsProbabilityMeasure (R j)]



end pull
end Bind
end YM.SectorNext.Reconnect
