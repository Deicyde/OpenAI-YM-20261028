import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07

/-!
# Stability language for common ordered extractions

A cutoff family is not changed. `f : YM.Extraction.Order` picks a common mesh
subsequence at *every* fixed period, and a period subsequence (outer limit).
We also allow refinements up to ignoring finite prefixes, useful when different
stages need more auxiliary data. Both sequences must refine *separately*;
using a diagonal in the (cutoff, period) pairs would not preserve the
semantics of the estimates.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Next.Extract
open Extraction Set Function Filter
open scoped Topology

/-- Sequence `s` refines `t` up to a finite prefix. -/
def Tail (s t : Sequence) : Prop := ∀ᶠ j : ℕ in atTop, s j ∈ range t

namespace Tail



lemma holds {s t : Sequence} (h : Tail s t) (P : ℕ → Prop) (H : ∀ᶠ i : ℕ in atTop, P (t i)) :
    ∀ᶠ j : ℕ in atTop, P (s j) := by
  obtain ⟨i,hi⟩ := eventually_atTop.mp H
  filter_upwards [h, s.cofinal.eventually_ge_atTop (t i)] with k hk hk'
  obtain ⟨j,hj⟩ := hk
  rw [← hj]
  exact hi _ (t.monotone.le_iff_le.mp (hj.symm ▸ hk'))

lemma converges {s t : Sequence} {X : Type*} [TopologicalSpace X] (h : Tail s t) (x : ℕ → X) {b : X}
    (H : Tendsto (fun j => x (t j)) atTop (𝓝 b)) : Tendsto (fun j => x (s j)) atTop (𝓝 b) :=
  tendsto_def.mpr fun K hK => h.holds (fun i => x i ∈ K) (H.eventually hK)

lemma trans {r s t : Sequence} (h : Tail r s) (w : Tail s t) : Tail r t :=
  h.holds (fun i => i ∈ range t) w

lemma after (s t : Sequence) : Tail (s.after t) s := Eventually.of_forall fun i => ⟨t i,rfl⟩
end Tail

/-- Needed to adapt estimates on a regulator-dependent row to a stricter
ordered extraction. Lift back only *on the range of the new grid*. This holds
for any two sequences. -/
lemma restricted (s t : Sequence) (P : ℕ → Prop) (h : ∀ᶠ i : ℕ in atTop, P (s i)) :
    ∀ᶠ j : ℕ in atTop, t j ∈ range s → P (t j) := by
  obtain ⟨i,hi⟩ := eventually_atTop.mp h
  filter_upwards [t.cofinal.eventually_ge_atTop (s i)] with k hk H
  obtain ⟨j,hj⟩ := H
  rw [← hj]
  exact hi _ (s.monotone.le_iff_le.mp (hj.symm ▸ hk))

structure Tails (g f : Order) : Prop where
  mesh : Tail g.mesh f.mesh
  per : Tail g.per f.per

/-- The actual indices picked by an ordered extraction (not `order.fuse`, a
filter; this is just its product grid). -/
def picks (g : Order) (N p : ℕ) : Prop := N ∈ range g.mesh ∧ p ∈ range g.per

lemma picks_self (g : Order) (j k : ℕ) : picks g (g.mesh j) (g.per k) :=
  ⟨mem_range_self j, mem_range_self k⟩

lemma localize (g f : Order) {A : ℕ → ℕ → Prop} (h : g.late A) :
    f.late fun N p => picks g N p → A N p := by
  unfold Order.late at *
  filter_upwards [restricted g.per f.per (fun p => ∀ᶠ j : ℕ in atTop, A (g.mesh j) p) h] with k hk
  by_cases hp : f.per k ∈ range g.per
  · filter_upwards [restricted g.mesh f.mesh (fun N => A N (f.per k)) (hk hp)] with j hj ha using hj ha.1
  exact Eventually.of_forall fun j ha => (hp ha.2).elim

namespace Tails
variable {f g r : Order}


lemma trans (u : Tails r g) (h : Tails g f) : Tails r f := ⟨u.mesh.trans h.mesh, u.per.trans h.per⟩
lemma refine (f g : Order) : Tails (f.refine g) f := ⟨Tail.after _ _, Tail.after _ _⟩

lemma late (h : Tails g f) {A : ℕ → ℕ → Prop} (H : f.late A) : g.late A :=
  (h.per.holds (fun p => ∀ᶠ j : ℕ in atTop, A (f.mesh j) p) H).mono fun k hk =>
    h.mesh.holds (fun N => A N (g.per k)) hk

lemma fused (h : Tails g f) : g.fuse ≤ f.fuse := fun _ hs =>
  Order.fused g _ |>.2 (h.late ((Order.fused f _).mp hs))

lemma limits {X : Type*} [TopologicalSpace X] (h : Tails g f) {A W} {x : X} (H : f.limits A W x) : g.limits A W x := by
  obtain ⟨he,v,hv,hl⟩ := H
  exact ⟨h.per.holds _ he,v,fun p hp => h.mesh.converges (fun N => W N p) (hv p hp), h.per.converges v hl⟩
end Tails

end YM.Next.Extract
