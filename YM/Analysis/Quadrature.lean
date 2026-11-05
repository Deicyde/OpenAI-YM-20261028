import YM.Analysis.Nonnegative
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Quadrature without exact finite-support assumptions

Use for finite cyclic integrals; simultaneous for every fixed continuous integrand,
no uniformity in mesh/period/gaps given. Boundary/point arguments comparing
neighboring lattice moves must take their quadrature limit *at fixed* regulators first.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Analysis
open Filter Function MeasureTheory Set Metric TopologicalSpace
open scoped Topology BigOperators ENNReal NNReal ComplexOrder

variable (X : Type*) [MeasurableSpace X]

/-- May include empty cells/zero masses. -/
structure Quad where
  size : ℕ
  slice : X → Fin size
  tag : Fin size → X
  cuts : Measurable slice

namespace Quad
variable {X} (Q : Quad X)

def map (x : X) := Q.tag (Q.slice x)
def tile (i : Fin Q.size) := Q.slice ⁻¹' {i}

@[fun_prop] lemma meas_map : Measurable Q.map := measurable_of_finite Q.tag |>.comp Q.cuts
lemma tile_meas (i) : MeasurableSet (tile Q i) := Q.cuts (measurableSet_singleton _)

section
variable [MetricSpace X] [BorelSpace X] [CompactSpace X]

lemma refine_ (ε : ℝ) (he : 0 < ε) : ∃ Q : Quad X, ∀ x, dist x (Q.map x) < ε := by
  classical
  obtain ⟨X', hX⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ball x ε) (fun _ => isOpen_ball)
    (fun (x : X) _ => mem_iUnion.mpr ⟨x,mem_ball_self he⟩)
  let B := Fintype.equivFin X'
  let r := fun i => (B.symm i).val
  let A := fun i => ball (r i) ε
  have hu (x : X) : ∃ i, x ∈ A i := by
    have H := hX (mem_univ x)
    obtain ⟨i,hi,he⟩ : ∃ i ∈ X', x ∈ ball i ε := by simpa using H
    refine ⟨B ⟨i,hi⟩,?_⟩
    simp [A,r,he]
  let D := disjointed A
  have HH : (⋃ i, D i) = univ := by
    unfold D; rw [iUnion_disjointed]; exact Set.eq_univ_of_forall fun x => mem_iUnion.mpr (hu x)
  choose p hp using fun (x : X) => show ∃ i, x ∈ D i from mem_iUnion.mp (HH.symm ▸ mem_univ x)
  have hm : Measurable p := by
    apply measurable_to_countable'
    intro i
    rw [show p ⁻¹' {i} = D i by
      ext x; simp only [mem_preimage, mem_singleton_iff]; exact ⟨fun h => h ▸ hp x,
        fun he => by_contra fun w => disjoint_left.mp (disjoint_disjointed A w) (hp x) he⟩]
    exact disjointedRec (f := A) (p := MeasurableSet) (fun _ _ ht => MeasurableSet.diff ht isOpen_ball.measurableSet) (show MeasurableSet (A i) from isOpen_ball.measurableSet)
  exact ⟨⟨_,p,r,hm⟩, fun x => mem_ball.mp (disjointed_subset A _ (hp x))⟩

variable (X) in
def shrink (k : ℕ) : Quad X := (refine_ (X := X) ((k:ℝ)+1)⁻¹ (by positivity)).choose

lemma along (x : X) : Tendsto (fun k => (shrink X k).map x) atTop (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have he : Tendsto (fun i : ℕ => (i:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right _ _ (show Tendsto ((↑) : ℕ → ℝ) atTop atTop from tendsto_natCast_atTop_atTop)
  refine squeeze_zero (fun _ => dist_nonneg) (fun i => ?_)
    (g := fun i : ℕ => ((i:ℝ)+1)⁻¹) (tendsto_inv_atTop_zero.comp he)
  rw [dist_comm]; exact ((refine_ _ (by positivity)).choose_spec x).le
end

variable (μ : Measure X) [IsFiniteMeasure μ]

def mass (i : Fin Q.size) : ℝ := μ.real (Q.tile i)

omit [IsFiniteMeasure μ] in
lemma mass_nonneg (i) : 0 ≤ mass Q μ i := measureReal_nonneg

protected lemma count {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (f : X → Y) : (∫ x, f (map Q x) ∂μ) = ∑ i, mass Q μ i • f (Q.tag i) := by
  classical
  rw [show (fun x => f (map Q x)) = (fun x => ∑ i, (tile Q i).indicator (fun _ => f (Q.tag i)) x) by
    funext x
    rw [Finset.sum_eq_single_of_mem (Q.slice x) (Finset.mem_univ _), indicator_of_mem (show x∈tile Q _ from mem_singleton _)]
    · rfl
    · intro i _ h; rw [indicator_of_notMem (show x∉tile Q _ from fun w => h (Set.mem_singleton_iff.mp w).symm)]]
  rw [integral_finsetSum _ (fun i _ => (integrable_const _).indicator (Q.tile_meas i))]
  exact Finset.sum_congr rfl fun i _ => (integral_indicator (Q.tile_meas i)).trans (setIntegral_const ..)

/-- All variables of a product Haar integral at once. -/
lemma counting {ι Y : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (g : (ι → X) → Y) :
    (∫ x : ι → X, g (fun i => map Q (x i)) ∂(Measure.pi fun _ => μ)) =
      ∑ i : ι → Fin Q.size, (∏ j, mass Q μ (i j)) • g (fun j => Q.tag (i j)) := by
  classical
  let S := Fintype.equivFin (ι → Fin Q.size)
  let P : Quad (ι → X) :=
    { size := Fintype.card (ι → Fin Q.size)
      slice := fun p => S (fun j => Q.slice (p j))
      tag := fun i j => Q.tag ((S.symm i) j)
      cuts := (measurable_of_finite S).comp (measurable_pi_lambda _ fun i => Q.cuts.comp (measurable_pi_apply i)) }
  have he (x : ι → X) : (fun i => Q.map (x i)) = P.map x := by simp [P,map]
  simp_rw [he,P.count (Measure.pi (fun _ : ι => μ))]
  symm; apply Fintype.sum_equiv S
  intro i
  have hl : P.tile (S i) = Set.pi univ (fun j => Q.tile (i j)) := by
    ext x
    simp only [tile,P,mem_preimage,mem_singleton_iff,S.injective.eq_iff,Set.mem_pi,mem_univ,forall_true_left]; exact funext_iff
  dsimp only [mass]
  simp [hl,P,measureReal_def, Measure.pi_pi,ENNReal.toReal_prod]

variable [MetricSpace X] [BorelSpace X] [CompactSpace X] [SecondCountableTopology X]

/-- Simultaneous approximation for continuous functions on any finite product. -/
theorem approximation {ι Y : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (F : (ι → X) → Y) (H : Continuous F) :
    Tendsto (fun k => ∑ i : ι → Fin (shrink X k).size, (∏ j, mass (shrink X k) μ (i j)) •
      F (fun j => (shrink X k).tag (i j))) atTop (𝓝 (∫ x, F x ∂(Measure.pi fun _ : ι => μ))) := by
  simp_rw [← counting]
  obtain ⟨c,hc⟩ := H.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  refine tendsto_integral_of_dominated_convergence (fun _ => c) ?_ (integrable_const _) ?_ ?_
  · intro i
    have hp := H.stronglyMeasurable
    exact (hp.comp_measurable (measurable_pi_lambda _ fun a => (meas_map (shrink X i)).comp
      (measurable_pi_apply a))).aestronglyMeasurable
  · exact fun i => Eventually.of_forall fun x => hc _
  refine Eventually.of_forall fun x => ?_
  exact H.continuousAt.tendsto.comp (show Tendsto (fun i (a : ι) => map (shrink X i) (x a)) atTop (𝓝 x)
    from tendsto_pi_nhds.mpr fun i => along _)
end Quad
end YM.Analysis
