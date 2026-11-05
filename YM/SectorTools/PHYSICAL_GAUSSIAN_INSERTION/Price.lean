import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Law

/-!
# Volume and spectral units of a local comparison

Counting metric only. Marginal data and the *p test on those marginal
data* should be controlled independently of the volume if wanting a uniform
estimate. Here is one sufficient explicit price, meaningful up to an
arbitrary positive margin at the threshold. No assumption of small
perturbation. Need of course to price the actual restricted shift too.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianInsertion

open Function Filter Set Matrix MeasureTheory
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian
open FreeResolvent (Gap normSum_nn)
open scoped Topology BigOperators Classical ENNReal RealInnerProductSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A D : Gaussian.Table ι}
  {a d h : Vec ι} {e₁ e₂ δ K p q : ℝ}

/-- Counting upper form bound. Positivity assumptions separate. -/
def Ceiling (A : Gaussian.Table ι) (K : ℝ) := ∀ v : Vec ι, quad A v ≤ K * (v ⬝ᵥ v)



omit [DecidableEq ι] in
lemma posDef_of_gap (hh : Gap A K) (he : A.IsSymm) (hp : 0 < K) : A.PosDef :=
  posDef_of_quad_pos he fun x hx => lt_of_lt_of_le
    (mul_pos hp ((normSum_nn x).lt_of_ne fun h => hx (dotProduct_self_eq_zero.mp h.symm))) (hh.lower x)

lemma inv_action (hA : A.PosDef) (x : Vec ι) : A *ᵥ (A⁻¹ *ᵥ x) = x := by
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hA.det_pos.ne'), one_mulVec]

/-- Rayleigh-type inequality, use with a trial `y` for lower bounds on
precision. -/
lemma variational (hA : A.PosDef) (y x : Vec ι) : 2*(y ⬝ᵥ x) - quad A y ≤ quad A⁻¹ x := by
  let z := A⁻¹ *ᵥ x
  have hb : A *ᵥ z = x := inv_action hA x
  have he : quad A z = quad A⁻¹ x := by unfold quad; rw [hb, dotProduct_comm z]
  have ht := quad_nonneg hA (y + -z)
  rw [quad_add (isHermitian_iff_isSymm.mp hA.isHermitian), mulVec_neg, hb,
    dotProduct_neg, show quad A (-z) = quad A z by simp only [quad, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg], he] at ht
  linarith

lemma inv_gap (hA : A.PosDef) (hh : Ceiling A K) (hp : 0 < K) : Gap A⁻¹ K⁻¹ := by
  constructor
  intro x
  have he := variational hA (K⁻¹ • x) x
  have hu : quad A (K⁻¹ • x) ≤ K⁻¹ * (x ⬝ᵥ x) := calc
    _ = K⁻¹^2 * quad A x := quad_smul ..
    _ ≤ K⁻¹^2 * (K*(x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left (hh x) (sq_nonneg _)
    _ = _ := by field_simp
  change _ ≤ quad A⁻¹ x
  rw [smul_dotProduct, smul_eq_mul] at he
  linarith only [hu, he]





-- One-sided variants (cf. `VACUUM_NORMALIZATION.Panel.bill_quad`).










variable {S : Finset ι} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {F : Vec ι → X}



end YM.SectorTools.PhysicalGaussianInsertion
