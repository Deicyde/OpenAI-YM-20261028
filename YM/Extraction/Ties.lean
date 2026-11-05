import YM.Extraction.Patch
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Discard coordinate ties under separated integration

They have zero volume at each fixed period as well as in infinite space.
This does *not* discard point-like insertions in later arguments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open MeasureTheory Set Filter
open scoped Topology

variable {n : ℕ}

private theorem flat_zero (p q : Fin n) (hp : p ≠ q) (i : Axis) (k : ℝ) :
    volume {x : Points n | x p i - x q i = k} = 0 := by
  let f : Points n →ₗ[ℝ] ℝ :=
    ((EuclideanSpace.proj i).toLinearMap).comp ((PiLp.projₗ (𝕜 := ℝ) 2 (fun _ => E4) p) - PiLp.projₗ (𝕜 := ℝ) 2 (fun _ => E4) q)
  let y (k : ℝ) := points <| Pi.single p (k • basis i)
  have he (x : Points n) : x p i - x q i = f x := rfl
  have hy (t : ℝ) : f (y t) = t := by rw [← he]; simp [y,Pi.single_eq_of_ne hp.symm]
  let M := AffineSubspace.mk' (y k) (LinearMap.ker f)
  have H (x : Points n) : x ∈ M ↔ x p i - x q i = k := by
    rw [he, AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker, map_sub, hy, sub_eq_zero]
  rw [show {x : Points n | x p i - x q i = k} = M from Set.ext fun i => (H i).symm]
  apply Measure.addHaar_affineSubspace
  intro hx
  have hg := (H (y (k+1))).mp (hx.symm ▸ AffineSubspace.mem_top _ _ _)
  rw [he, hy] at hg; linarith

theorem almostCyclic (S : Schedule) (p n : ℕ) : ∀ᵐ x : Points n, x ∈ Cyclic S p n := by
  have he (i j : Fin n) (h : i ≠ j) (a : Axis) : ∀ᵐ x : Points n, ¬ periodic S p (x i a) (x j a) := by
    have hh (k : ℤ) : ∀ᵐ x : Points n, x i a - x j a ≠ k * length S p := by
      rw [ae_iff]; simpa using flat_zero i j h a (k*length S p)
    filter_upwards [ae_all_iff.mpr hh] with x hx hX
    obtain ⟨j,H⟩ := hX
    exact hx j H
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun h => ae_all_iff.mpr (he i j h))))] with x hx
  exact hx

theorem almostGeneric (n : ℕ) : ∀ᵐ x : Points n, x ∈ generic n := by
  have he (i j : Fin n) (h : i ≠ j) (a : Axis) : ∀ᵐ x : Points n, x i a - x j a ≠ 0 := by
    rw [ae_iff]; simpa using flat_zero i j h a 0
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun h => ae_all_iff.mpr (he i j h))))]
    with x hx
  exact fun a i j ht => by_contra fun w => hx i j w a (sub_eq_zero.mpr ht)
end YM.Extraction
