import YM.Push.SECTOR_MEASURE.Decompose

/-!
# Common tag, law and the tie to the interacting step

The reference on
predictor choices is uniform (includes all choices including unused) -- thus where
needed the integrand must contain the likelihood **relative to
that**.

Prove conversion from/through the actual code's counting convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Lattice RG Wilson Precision Module Push.SectorMeasure Tree
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {m n : Side}
structure Keyed (S : StepData m n) where
  key : S.Choices
namespace Keyed
variable (S : StepData m n)
def equiv : Keyed S ≃ S.Choices := ⟨Keyed.key,Keyed.mk,fun _ => rfl,fun _ => rfl⟩
instance : Fintype (Keyed S) := Fintype.ofEquiv _ (equiv S).symm
instance : MeasurableSpace (Keyed S) := ⊤
instance : MeasurableSingletonClass (Keyed S) := ⟨fun _ => trivial⟩
instance : Nonempty (Keyed S) := (equiv S).nonempty

def card : ℝ := Fintype.card (Keyed S)
lemma card_pos : 0 < card S := Nat.cast_pos.mpr Fintype.card_pos
lemma card_eq : card S = Fintype.card S.Choices := by unfold card; rw [Fintype.card_congr (equiv S)]

def primary : Measure (Keyed S) := ENNReal.ofReal (card S)⁻¹ • Measure.count
instance : IsProbabilityMeasure (primary S) := ⟨by
  have hs : Measure.count (Set.univ : Set (Keyed S))= ENNReal.ofReal (card S) := by simp [Measure.count_apply_finite _ (Set.toFinite _),card]
  have he : 0<card S := card_pos S
  unfold primary; rw [Measure.smul_apply, hs, smul_eq_mul,← ENNReal.ofReal_mul (by positivity),inv_mul_cancel₀ he.ne',ENNReal.ofReal_one]⟩

variable {E : Type*} [NormedAddCommGroup E]
lemma integrable (f : Keyed S → E) : Integrable f (primary S) := by
  unfold primary
  exact (integrable_count_iff.mpr (summable_of_hasFiniteSupport (Set.toFinite _))).smul_measure (by finiteness)

variable [NormedSpace ℝ E] [CompleteSpace E]

lemma total (f : S.Choices → E) : (∫ k,card S • f k.key ∂primary S) = ∑ k,f k := by
  unfold primary; rw [integral_smul,integral_smul_measure,ENNReal.toReal_ofReal (inv_pos.mpr (card_pos S)).le,
    smul_smul, mul_inv_cancel₀ (card_pos S).ne',one_smul,integral_count]; exact Equiv.sum_comp (equiv S) f





lemma holds (F : Forest S.ratio) (f : S.Choices → F.Slice G → E) (h : ∀ k,Integrable (f k) (F.order G)) :
    tagTotal F f = (∫ k, ∫ y,card S • f k.key y ∂F.order G ∂primary S) ∧
    (∀ k, Integrable (fun y => card S • f k y) (F.order G)) ∧
    Integrable (fun k => ∫ y,card S • f k.key y ∂F.order G) (primary S) := by
  refine ⟨?_,fun k => Integrable.smul (card S) (h k), Keyed.integrable ..⟩
  simpa only [integral_smul] using! (Keyed.total S (fun i => ∫ y,f i y ∂F.order G)).symm



end Keyed
end YM.Further.DenseMixedKernels
