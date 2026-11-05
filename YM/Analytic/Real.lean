import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Matrix.PosDef



/-! # Neighborhood recognition of strict Hessian in Taylor ports -/
noncomputable section
namespace YM.Analytic
open Filter Topology Set InnerProductSpace Matrix
open scoped InnerProductSpace

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]



def stamp {m : ℕ} (b : Module.Basis (Fin m) ℝ F) (f : F → ℝ) (x : F) :
    Matrix (Fin m) (Fin m) ℝ := fun i j => iteratedFDeriv ℝ 2 f x ![b i,b j]

omit [FiniteDimensional ℝ F] in
theorem positive_stamp {m : ℕ} (b : Module.Basis (Fin m) ℝ F) (f : F → ℝ) (x : F)
    (h : AnalyticAt ℝ f x) (hp : ∀ v : F, v ≠ 0 → 0 < iteratedFDeriv ℝ 2 f x ![v,v]) :
    0 < Matrix.det (stamp b f x) := by
  apply Matrix.PosDef.det_pos
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  have hs := h.contDiffAt.isSymmSndFDerivAt (n := 2) (by simp)
  constructor
  · ext i j
    simp only [stamp,Matrix.conjTranspose_apply, star_trivial, iteratedFDeriv_two_apply]
    exact hs ..
  intro y hy
  have hn : ∑ i, y i • b i ≠ 0 := by
    intro hn; apply hy; funext l
    have he := DFunLike.congr_fun (congrArg b.repr hn) l
    simpa [Finsupp.single_apply] using he
  let a := fderiv ℝ (fderiv ℝ f) x
  have he : star y ⬝ᵥ ((stamp b f x) *ᵥ y) = iteratedFDeriv ℝ 2 f x
      ![∑ i, y i • b i, ∑ i, y i • b i] := by
    -- expand both slots
    unfold dotProduct Matrix.mulVec stamp
    simp only [dotProduct,Pi.star_apply,star_trivial,iteratedFDeriv_two_apply]
    change ∑ i, y i * (∑ j, a (b i) (b j) * y j) = a (∑ i, y i • b i) (∑ j, y j • b j)
    simp [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [he]; exact hp _ hn
end YM.Analytic
