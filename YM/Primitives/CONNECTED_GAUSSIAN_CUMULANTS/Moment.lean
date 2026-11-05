import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Probe
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Trace

/-!
# One joint representation for all submoments

A general correlated Gaussian rule for the `T` occurrences. Here the same
weight must pay across the occurrences, not a separate bound for each probe.
It passes to any of the requested submoments too. No cost in the number of
auxiliary dimensions `J`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open MeasureTheory ProbabilityTheory Filter Function Finset Set
open YM.Multi.Vacuum.Gauss Probe Quadratic
open scoped Topology BigOperators

variable {I J V : Type} [Fintype I] [Fintype J]
namespace Moment

def base (q : Rows V I J) (s : Finset V) (w : V → Row I) :=
    Ready (s ×ˢ (Finset.univ:Finset I)) (uncurry q) (uncurry w)

def sumCharge (s : Finset V) (q : Rows V I J) (w : V → Row I) := fun x =>
  ∑ i∈s,pay (w i) (mapRows (q i) x)

def due (s : Finset V) (q : Rows V I J) (w : V → Row I) :=
  ∑ i∈s,∑ a,w i a * squares (q i a)

def values (s : Finset V) (q : Rows V I J) (v : Probes V I) := fun x => ∏ i∈s,v i (mapRows (q i) x)
def total (s : Finset V) (q : Rows V I J) (v : Probes V I) := ∫ x,values s q v x ∂standard J

omit [Fintype I] in
lemma total_empty (q : Rows V I J) (v : Probes V I) : total ∅ q v=1 := by simp [total,values]

variable {s T : Finset V} {q : Rows V I J} {w : V → Row I} {H : V → ℕ → ℝ} {v : Probes V I} {n : ℕ}

lemma stack (s : Finset V) (q : Rows V I J) (w : V → Row I) (x : Row J) :
    exponent (s ×ˢ Finset.univ) (uncurry q) (uncurry w) x=sumCharge s q w x := by
  rw [Quadratic.exponent,sum_product]; rfl

lemma charge (s : Finset V) (q : Rows V I J) (w : V → Row I) :
    trace (s ×ˢ Finset.univ) (uncurry q) (uncurry w)=due s q w := by rw [Quadratic.trace,sum_product]; rfl

lemma base.nn (h : base q s w) {i : V} (hi : i∈s) (a : I) : 0 ≤ w i a :=
  h.1 (i,a) (mem_product.mpr ⟨hi,mem_univ a⟩)

lemma base.le (h : base q s w) {i : V} (hi : i∈s) (a : I) :
    ∑ j∈s,∑ b,w j b * |crossed (q i a) (q j b)| ≤ 1/8 := by
  have hr := h.2 (i,a) (mem_product.mpr ⟨hi,mem_univ a⟩)
  rw [sum_product] at hr; exact hr

lemma base.of (he : ∀ i∈s, ∀ a : I,0≤ w i a)
    (hl : ∀ i∈s,∀ a : I,∑ j∈s,∑ b,w j b * |crossed (q i a) (q j b)| ≤ 1/8) : base q s w := by
  refine ⟨fun p hp => he p.1 (mem_product.mp hp).1 p.2,?_⟩
  intro p hp; rw [sum_product]; exact hl p.1 (mem_product.mp hp).1 p.2

lemma base.small (h : base q s w) (x) : sumCharge s q w x ≤ 1/8*squares x :=
    (stack s q w x) ▸ Quadratic.ready_pays _ _ _ h x

lemma base.restrict (h : base q T w) (hs : s⊆T) : base q s w := by
  apply of (fun i hi => h.nn (hs hi))
  intro i hi a; apply le_trans _ (h.le (hs hi) a)
  exact sum_le_sum_of_subset_of_nonneg hs fun j hj _ => sum_nonneg fun b _ => mul_nonneg (h.nn hj b) (abs_nonneg _)

lemma amount (h : base q s w) :
    Integrable (fun x => Real.exp (sumCharge s q w x)) (standard J) ∧
    (∫ x,Real.exp (sumCharge s q w x) ∂standard J) ≤ Real.exp (2*due s q w) := by
  have hx := authentic _ _ _ h
  simp_rw [stack,charge] at hx; exact hx

omit [Fintype I] in
lemma map_cont (q : I → Row J) : Continuous (mapRows q) := by unfold mapRows crossed; fun_prop
omit [Fintype I] in
lemma values_continuous (h : ∀ i∈s,Continuous (v i)) (q : Rows V I J) : Continuous (values s q v) :=
  continuous_finsetProd _ fun i hi => (h i hi).comp (map_cont _)

variable [DecidableEq I]

lemma value_bound (hs : s ⊆ T) (h : Valid T n v w H) (q : Rows V I J) (x) :
    ‖values s q v x‖ ≤ (∏ i∈s,H i 0) * Real.exp (sumCharge s q w x) := by
  unfold sumCharge; rw [Real.exp_sum,← prod_mul_distrib]
  exact (Finset.norm_prod_le ..).trans (prod_le_prod (fun _ _ => norm_nonneg _) (fun i hi => h.pay i (hs hi) _))

lemma revenues (hx : base q T w) (h : Valid T n v w H) (hs : s⊆T) :
    Integrable (values s q v) (standard J) ∧
    (∫ x,‖values s q v x‖ ∂standard J) ≤ (∏ i∈s,H i 0)*Real.exp (2*due s q w) := by
  obtain ⟨he,hy⟩ := amount (hx.restrict hs)
  have ha := he.const_mul (∏ i∈s,H i 0)
  have hi : Integrable (values s q v) (standard J) := ha.mono'
    (values_continuous (fun i hi => h.read i (hs hi)) q).aestronglyMeasurable
    (Filter.Eventually.of_forall (value_bound hs h q))
  refine ⟨hi,(integral_mono hi.norm ha (value_bound hs h q)).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hy (prod_nonneg fun i hi => (h.guard i (hs hi)).fees 0)



-- Next proofs need Growth at finite volume and all interpolation t.
section
variable {S : Type*} (U : Set S) (L : S → Rows V I J)
lemma values_growth (hs : s ⊆ T) (h : Valid T n v w H) :
    Growth U (fun t => sumCharge s (L t) w) (fun t => values s (L t) v) :=
  Growth.plain (prod_nonneg fun i hi => (h.guard i (hs hi)).fees 0) fun _ _ => value_bound hs h _
omit [DecidableEq I] in
lemma works (hs : s ⊆ T) (hl : ∀ t∈U,base (L t) T w) : ExpPays U (fun t => sumCharge s (L t) w) :=
  ⟨1/8,by norm_num,fun t ht => ((hl t ht).restrict hs).small⟩

lemma total_stays [TopologicalSpace S] [FirstCountableTopology S]
    (hs : s ⊆ T) (h : Valid T n v w H) (hl : ∀ t∈U,base (L t) T w)
    (hc : ∀ i∈s, ∀ a : I, Continuous fun t => L t i a) :
    ContinuousOn (fun t => total s (L t) v) U := by
  refine (values_growth U L hs h).continuity (works U L hs hl)
    (fun t ht => values_continuous (fun i hi => h.read i (hs hi)) _) ?_
  intro x
  apply Continuous.continuousOn
  apply continuous_finsetProd
  intro i hi
  apply Continuous.comp (h.read i (hs hi))
  apply continuous_pi; intro a
  change Continuous fun t => crossed (L t i a) x
  simp_rw [crossed_comm _ x]
  exact (crossed_cont x).comp (hc i hi a)
end
end Moment
end YM.Primitives.GCC
