import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.A15
import YM.Work.B04

/-!
# Small library of finite-volume bounds for actual pullbacks/products.

These `Envelope`s include genuine everywhere bounds/Borel measurability, not
bounds almost everywhere; they do NOT automatically come with any uniformity
across cutoffs.
-/

set_option autoImplicit false
noncomputable section

namespace YM.RG.Envelope
open Function MeasureTheory Filter
open scoped Topology BigOperators

variable {X Y : Type*} [MeasurableSpace X]

lemma comp_env [MeasurableSpace Y] {Z : Type*} [MeasurableSpace Z] [Norm Z]
    {f : Y → Z} (h : Envelope f) {g : X → Y} (e : Measurable g) : Envelope (fun x => f (g x)) := by
  obtain ⟨C,H⟩ := h.cost
  exact ⟨h.meas.comp e, C, fun x => H (g x)⟩

variable {f g : X → ℂ}

lemma constC (c : ℂ) : Envelope (fun _ : X => c) := ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

lemma compactC [TopologicalSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    (h : Continuous f) : Envelope f := by
  obtain ⟨C,H⟩ := (isCompact_range h.norm).bddAbove
  exact ⟨h.measurable, C, fun x => H ⟨x,rfl⟩⟩

lemma ofReal_env {f : X → ℝ} (h : Envelope f) : Envelope (fun x => (f x : ℂ)) := by
  obtain ⟨C,H⟩ := h.cost
  exact ⟨Complex.continuous_ofReal.measurable.comp h.meas, C, fun x => by simpa using H x⟩

lemma addC (h : Envelope f) (e : Envelope g) : Envelope (fun x => f x + g x) := by
  obtain ⟨C,H⟩ := h.cost; obtain ⟨D,E⟩ := e.cost
  exact ⟨h.meas.add e.meas, C+D, fun x => (norm_add_le ..).trans (add_le_add (H x) (E x))⟩

lemma negC (h : Envelope f) : Envelope (fun x => - f x) := by
  obtain ⟨C,H⟩ := h.cost
  exact ⟨h.meas.neg, C, fun x => by simpa using H x⟩

lemma subC (h : Envelope f) (e : Envelope g) : Envelope (fun x => f x - g x) := by
  simp only [sub_eq_add_neg]; exact h.addC e.negC

lemma mulC (h : Envelope f) (e : Envelope g) : Envelope (fun x => f x * g x) := by
  obtain ⟨C,H⟩ := h.cost; obtain ⟨D,E⟩ := e.cost
  exact ⟨h.meas.mul e.meas, C*D, fun x => (norm_mul_le ..).trans
    (mul_le_mul (H x) (E x) (norm_nonneg _) ((norm_nonneg _).trans (H x)))⟩

lemma starC (h : Envelope f) : Envelope (fun x => star (f x)) := by
  obtain ⟨C,H⟩ := h.cost
  exact ⟨continuous_star.measurable.comp h.meas, C, fun x => by simpa using H x⟩

lemma sumC {ι : Type*} (s : Finset ι) (f : ι → X → ℂ) (h : ∀ i∈s, Envelope (f i)) :
    Envelope (fun x => ∑ i∈s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (constC (X:=X) 0)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).addC (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma prodC {ι : Type*} (s : Finset ι) (f : ι → X → ℂ) (h : ∀ i∈s, Envelope (f i)) :
    Envelope (fun x => ∏ i∈s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (constC (X:=X) 1)
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self ..)).mulC (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma integrableC (hf : Envelope f) (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨C,H⟩ := hf.cost
  exact Integrable.of_bound hf.meas.aestronglyMeasurable C (Eventually.of_forall H)
end YM.RG.Envelope

namespace YM.Push.GridApprox
open Function MeasureTheory RG Lattice Wilson Cells

lemma cylinder_env {G : Gauge} {n : Side} {X} {F : Config G n → ℂ} (h : Interior X F) : Envelope F :=
  ⟨h.borel, h.cost⟩

lemma replica_env {G : Gauge} {n : Side} (T : Tiling n) (v : T.Cell) {F : Config G n → ℂ}
    (h : Envelope F) : Envelope (T.copy v F) := by
  classical
  have ht := h.comp_env (continuous_pull (G:=G) (T.omega v) (T.translateBy v)).measurable
  unfold Tiling.copy
  by_cases hc : T.hand v <;> simp only [hc,↓reduceIte]; exacts [ht.starC, ht]

end YM.Push.GridApprox
