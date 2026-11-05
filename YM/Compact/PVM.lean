import YM.Compact.Borel
import YM.Spectral.Projection

/-!
# Compact-model strong countable additivity
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spectral.Rep
open MeasureTheory Measure Filter Set Function Complex
open scoped Topology NNReal ENNReal Real BigOperators InnerProductSpace symmDiff
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  {H : Hilbert} (A : CC X →⋆ₐ[ℂ] H.Op)

omit [TopologicalSpace X] [T2Space X] [BorelSpace X] [CompactSpace X] in
lemma unites (μ : Measure X) [IsFiniteMeasure μ] (s : ℕ → Set X) (hp : ∀ i, MeasurableSet (s i))
    (h : Pairwise (Disjoint on s)) : HasSum (fun i => blob μ (hp i)) (blob μ (MeasurableSet.iUnion hp)) := by
  let N (t : Finset ℕ) := ⋃ k ∈ t, s k
  have ht (t : Finset ℕ) : MeasurableSet (N t) := t.measurableSet_biUnion fun i _ => hp i
  have ho : Monotone N := fun t r hr => iUnion₂_mono' fun i hi => ⟨i,hr hi,Set.Subset.rfl⟩
  have hb t : N t ⊆ ⋃ i, s i := iUnion₂_subset fun i _ => subset_iUnion _ _
  have hU : (⋃ t : Finset ℕ, N t)=⋃ i, s i := by
    refine le_antisymm (iUnion_subset hb) (iUnion_subset fun i => subset_trans ?_ (subset_iUnion N {i}))
    simp [N]
  have hv : Tendsto (fun t => μ (N t ∆ (⋃ i, s i))) atTop (𝓝 0) := by
    have he := tendsto_measure_iUnion_atTop (μ := μ) ho
    rw [hU] at he
    have hx t : μ (N t ∆ (⋃ i, s i))=μ (⋃ i, s i)-μ (N t) := by
      rw [symmDiff_def,Set.sdiff_eq_empty.mpr (hb t), show (∅ : Set X)=⊥ from rfl, bot_sup_eq]
      exact measure_sdiff (hb t) (ht t).nullMeasurableSet (measure_ne_top _ _)
    simp_rw [hx]
    have hz := ENNReal.Tendsto.sub (tendsto_const_nhds (x := μ (⋃ i, s i))) he
    simpa using hz (Or.inl (measure_ne_top μ (⋃ i, s i)))
  have hc : Tendsto (fun t => blob μ (ht t)) atTop (𝓝 (blob μ (MeasurableSet.iUnion hp))) :=
    tendsto_indicatorConstLp_set (by norm_num) hv
  apply hc.congr'
  apply Eventually.of_forall; intro t; change blob μ (ht t)= ∑ i ∈ t, blob μ (hp i)
  induction t using Finset.induction_on with
  | empty => simp [blob,N]
  | @insert i S hi ih =>
    have hg : Disjoint (s i) (N S) := disjoint_iUnion_right.mpr fun j => disjoint_iUnion_right.mpr fun hj =>
      h (show i≠j from fun p => hi (p ▸ hj))
    have hm : N (Insert.insert i S) = s i ∪ N S := by simp [N]
    rw [Finset.sum_insert hi,← ih]
    convert! indicatorConstLp_disjoint_union (hp i) (ht S) (measure_ne_top μ _) (measure_ne_top μ _) hg (1:ℂ) using 1
    all_goals unfold blob; congr 1

def zone (s : Set X) : H.Op := open scoped Classical in if h : MeasurableSet s then batch A h else 0
lemma at_borel {s : Set X} (h : MeasurableSet s) : zone A s=batch A h := dif_pos h

def ships : PVM H X where
  region := zone A
  none := (at_borel A MeasurableSet.empty).trans (nobody A)
  all := (at_borel A MeasurableSet.univ).trans (whole A)
  joins hs ht := by rw [at_borel _ hs,at_borel _ ht,at_borel _ (hs.inter ht),joins]
  real h := by rw [at_borel _ h,refl]
  unites s hs h x := by
    simp_rw [at_borel A (hs _),at_borel A (MeasurableSet.iUnion hs)] -- possible simp ht
    exact (J A x).hasSum (unites (sees A x) s hs h)
  diagonal := sees A
  finite x := inferInstance
  at_pair h x := by rw [at_borel _ h,inner']
end YM.Spectral.Rep
