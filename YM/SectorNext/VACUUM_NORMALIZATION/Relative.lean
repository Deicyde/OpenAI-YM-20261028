import YM.Push.SECTOR_MEASURE.Output
import YM.Push.SECTOR_MEASURE.Overlap
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped


/-!
# Normalizing the sectors *along the run*

Spending v's and likelihood/noise scales on the exact sector totals,
without taking logs of cutEntries. Real probability on (tag,store) at
every V. No airlift of an integral bound past normalizing by a V-density
without proof of the relationship. Also includes useful true density
majorant route for multiplier comparisons. Does not claim pointwise
relative smallness is the *only* or even an applicable route for every
correction (esp. near flags where the denominator is itself tiny).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open RG Wilson Lattice Pressure Pressure.Stores Tree MeasureTheory Filter Push.SectorMeasure
open  Next.Fluctuations.Sector
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ENNReal
variable {G : Gauge} {c f : Side} {S : StepData c f} {x W : ℝ}
  (D : Allocation G S x W) (F : Forest S.ratio) (β : ℝ)

/-- Factoring noise relative to a uniform tag reference; keep one
compensation by the cardinal of the reference alphabet (likelihood in
code lives against COUNTING, NOT uniform probability). Only at the
whole tag array, not a new iid assumption. -/
def broad (d : S.Choices) (U : Config G f) := Fintype.card S.Choices*S.likelihood U d

def tagRef (_d : S.Choices) : ℝ := (Fintype.card S.Choices:ℝ)⁻¹

private lemma card_tag (hm : S.patch.Branches S.kernel G) : (Fintype.card S.Choices:ℝ)≠0 := by
  obtain ⟨t,ht⟩ := exists_alive hm (1:Config G f)
  haveI := (⟨t⟩ : Nonempty S.Choices)
  exact_mod_cast Fintype.card_pos (α:=S.Choices) |>.ne'

lemma tag_density_paid (hm : S.patch.Branches S.kernel G) (d : S.Choices) (U : Config G f) :
    tagRef d * broad d U = S.likelihood U d := by
  rw [broad,tagRef,←mul_assoc,inv_mul_cancel₀ (card_tag hm),one_mul]
lemma reference_is_prob (hm : S.patch.Branches S.kernel G) : ∑ d : S.Choices,tagRef d=1 := by
  simp only [tagRef, Finset.sum_const,Finset.card_univ,nsmul_eq_mul, mul_inv_cancel₀ (card_tag hm)]


def post (d : S.Choices) (V : Config G c) (U : Config G f) :=
    Real.exp (-(Precision.noiseTaylor S V U d)*β)
lemma kernel_read (d : S.Choices) (U : Config G f) (V : Config G c) :
    taggedKernel S β d U V = prefactor S G β * (S.likelihood U d * post β d V U) := by
  unfold taggedKernel StepData.noise post StepData.penaltyWeight prefactor Precision.noiseTaylor
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,← Real.exp_sum,←Finset.mul_sum]
  rw [show -(_*(_ : ℝ))*β = -β*S.kernel.penalty*∑ i,G.price (V i*(S.prediction U d i)⁻¹) by ring]; ring

def balance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (g : Config G f → X) (A : Stores S) (d : S.Choices) (V : Config G c) :=
    ∫ a : F.Slice G,
      ((D.bill A d (F.drape a) V * broad d (F.drape a) * post β d V (F.drape a)) • g (F.drape a)) ∂F.order G

/-- This form can feed a conditional Gaussian producer. All constants
explicit, on all (A,V), not just probabilities or a.e.. -/
theorem balanced_column {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (hm : S.patch.Branches S.kernel G)
    (g : Config G f → X) (A : Stores S) (V : Config G c) :
    output D F β g A V = prefactor S G β • ∑ d,tagRef d • balance D F β g A d V := by
  unfold output Allocation.column tagTotal balance Allocation.portion through
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_smul,← integral_smul]
  apply integral_congr_ae; filter_upwards with a
  simp only [kernel_read,smul_smul]
  rw [show prefactor S G β * tagRef i * (D.bill A i _ _ * broad i _ * _) = prefactor S G β *
    (D.bill A i (F.drape a) V*(tagRef i * broad i (F.drape a))*post β i V (F.drape a)) by ring,
    tag_density_paid hm]; rw [mul_left_comm]; simp [mul_assoc]

theorem output_factors (R : Rep G f) (Z : Stores S) (V : Config G c) :
    output D F β R.eval Z V = Real.exp R.scalar * output D F β (stripped R) Z V := by
  unfold output Allocation.column tagTotal through Allocation.portion
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [←integral_const_mul]; refine integral_congr_ae (Eventually.of_forall (fun a => ?_))
  simp only [smul_eq_mul]; rw [← restore R (F.drape a)]; ring



section normmajor
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

















end normmajor





end YM.SectorNext.Vacuum
