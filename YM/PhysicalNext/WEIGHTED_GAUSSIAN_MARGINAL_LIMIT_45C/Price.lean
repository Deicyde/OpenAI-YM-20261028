import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Cylinder
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.TotalCost
import YM.Extra.ITERATION_NO_LOSS.Radius
import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Price



/-!
# Numerical prices on the two covariance marginals

All prices in this file are functions of the committed step data (entry
bound to be *earned* on both marginals in the application) and the allowed
read cardinality K, not the dimension of a full cloud. In particular the
upper covariance bound here is constant in x. This is essential; do not just
pay for arbitrary x^small room raised to a degree supplied later.

The corresponding mean price is in common normalized fluctuation units. We
earn it below even when retaining *any given* witnesses of the existing log
bound in `Workshop`, so don't have to run two comparisons at different
gauges/logs. This uses the odd part of that bound *for Gaussian likelihoods*
and the earned actual covariance entry price, not just bounded tests.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C
open Function Filter Set Matrix MeasureTheory
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian
open AnalyticBridge.LocalGaussianLaws
open SectorTools PhysicalGaussianInsertion
open scoped Topology BigOperators

variable {K : ℕ} {E x : ℝ}

/-- Real eventual rate. -/
def speed (x : ℝ) : ℝ := x ^ (-(7/64):ℝ)





/-- K is the read cardinality cap, E the *entry* bound on both
covariances. Use `topBill` for the upper counting quadratic form bound. -/
def topBill (K : ℕ) (E : ℝ) : ℝ := 1 + (K:ℝ) * E
lemma topBill_pos (K : ℕ) (hE : 0 ≤ E) : 0 < topBill K E := by unfold topBill; positivity

/-- Coefficient of squared counting norm in the exponential moment test. -/
def heat (K : ℕ) (E : ℝ) : ℝ := (8 * topBill K E)⁻¹
lemma heat_pos (K : ℕ) (hE : 0 ≤ E) : 0 < heat K E := by
  unfold heat; have := topBill_pos K hE; positivity
lemma heat_pays (K : ℕ) (hE : 0 ≤ E) : topBill K E * (2 * heat K E) = 1/4 := by
  unfold heat; have hs := topBill_pos K hE; field_simp; ring

/-- Sup price on the normalized mean shift. -/
def centerBill (K : ℕ) (E : ℝ) : ℝ := ((K:ℝ)*E)*(2*(K:ℝ)+2)
lemma centerBill_nonneg (K : ℕ) (hE : 0 ≤ E) : 0 ≤ centerBill K E := by unfold centerBill; positivity

variable {I : Type}

/-- Actual entries of a covariance table. -/
def Billed (C : Gaussian.Table I) (E : ℝ) : Prop := ∀ i j, |C i j| ≤ E

variable {C B : Gaussian.Table I}
variable [Fintype I]

lemma Billed.ceiling (hc : Billed C E) (hE : 0 ≤ E) (hK : Fintype.card I ≤ K) :
    Ceiling C (topBill K E) := by
  -- count in each row and column, apply standard Schur bound, no
  -- factor from the volume of the full covariance. Unit type for the
  -- trivial cost space, every index still counted.
  let cost : FreeResolvent.Cost Unit :=
    ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ => rfl, fun _ _ => rfl, by intros; norm_num⟩
  let r : I → Unit := fun _ => ()
  have hi : cost.Schur r r 0 (topBill K E) C := by
    apply Local.cheaply hE hc
    refine (mul_le_mul_of_nonneg_right (show (Fintype.card I:ℝ) ≤ K from Nat.cast_le.mpr hK) hE).trans ?_
    unfold topBill; linarith
  exact fun z => (le_abs_self _).trans (FreeResolvent.schur_qf cost r hi z)

variable [DecidableEq I]





variable {δ : Vec I}



/-- Data of the actual covariance marginal comparison, with prices. -/
structure Prices (K : ℕ) (E x : ℝ) (C B : Gaussian.Table I) (δ : Vec I) : Prop where
  high : 1 ≤ x
  entry_pos : 1 ≤ E
  counts : Fintype.card I ≤ K
  curved : C.PosDef
  free : B.PosDef
  curved_entry : Billed C E
  free_entry : Billed B E
  log_le (z) : |Real.log (Density.replace C B (-δ) z)| ≤ speed x*(2*(K:ℝ) + 2*Density.energy z)







end YM.PhysicalNext.WeightedGaussianMarginal45C
