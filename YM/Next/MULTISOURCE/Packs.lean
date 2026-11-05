import YM.Next.MULTISOURCE.Fibers
import YM.RG.History


/-!
# Finite bucketing at one step

Support and *actual retained inventory*, not just center. Extra tests
stay enforced (in the activities themselves as zeros elsewhere). Compression
is only an identity for evaluating the denominator and its tangents.
We have to write to actual legal addresses in THAT Rep when rendering any new
family. One simple sufficient allocation is `Room` below. It has to be bought
upstream. We never change a vacuum support/predicate mid-transfer.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi
open RG Wilson Lattice Filter Function MeasureTheory
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators

abbrev Pack (n : Side) := { P : Support n × Support n // P.2.Nonempty ∧ P.2 ⊆ P.1 }

namespace Pack
variable {n : Side} {G : Gauge}

abbrev zone (P : Pack n) : Support n := P.val.1
abbrev flagsAt (P : Pack n) := P.val.2

def ofAddress (A : Activities G n) (i : ℕ) : Pack n :=
  ⟨⟨(A.forced i).support, (A.forced i).inventory⟩, (A.forced i).inventory_ne, (A.forced i).inventory_sup⟩

def clears (L : Support n) := Finset.univ.filter fun b : Finset (Pack n) =>
  (b : Set (Pack n)).PairwiseDisjoint zone ∧ b.biUnion flagsAt=L

lemma labeled (P : Rep G n) (U : Config G n) (b : Finset ℕ) :
    P.activities.admissible P.p U b ↔ b.image (ofAddress P.activities) ∈ clears (flags P.p.threshold U) ∧
    Set.InjOn (ofAddress P.activities) b := by
  let k := ofAddress P.activities
  simp only [Activities.admissible, clears, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.PairwiseDisjoint]
  have he : (b.image k).biUnion flagsAt=b.biUnion (fun i => (P.activities.forced i).inventory) := by
    rw [Finset.image_biUnion]; rfl
  rw [he]
  constructor
  · rintro ⟨h,H⟩
    refine ⟨⟨?_,H⟩,?_⟩
    · rw [Finset.coe_image]; exact Set.Pairwise.image (show (b : Set ℕ).Pairwise _ from h)
    intro i hi j hj e
    by_contra hn
    obtain ⟨v,hv⟩ := (k i).property.1
    have hp : v∈(k i).zone := (k i).property.2 hv
    have hq : v∈(k j).zone := by rw [show k j=k i from e.symm]; exact hp
    exact Finset.disjoint_left.mp (h hi hj hn) hp hq
  rintro ⟨⟨h,H⟩, hI⟩
  refine ⟨?_, H⟩
  intro i hi j hj hn
  change Disjoint (k i).zone (k j).zone
  exact h (Finset.mem_image_of_mem k hi) (Finset.mem_image_of_mem k hj) (fun e => hn (hI hi hj e))

lemma neighborhood_meas (P : Pack n) (t : ℝ) :
    MeasurableSet {U : Config G n | P.zone ∩ flags t U = P.flagsAt} := by
  rw [show {U : Config G n | _} = ⋃ F : {F : Support n // P.zone ∩ F=P.flagsAt}, {U | flags t U=F.val} by
    ext u; simp only [Set.mem_iUnion, Set.mem_setOf_eq]; constructor
    · intro h; exact ⟨⟨_,h⟩,rfl⟩
    rintro ⟨F,h⟩; rw [h]; exact F.property]
  exact MeasurableSet.iUnion fun F => flags_measurable_eq ..

lemma neighborhood (b : Finset (Pack n)) (t : ℝ) : MeasurableSet {U : Config G n | b ∈ clears (flags t U)} := by
  by_cases h : (b : Set (Pack n)).PairwiseDisjoint zone
  · simp only [clears, Finset.mem_filter,Finset.mem_univ,true_and,h]
    simp_rw [eq_comm]
    exact flags_measurable_eq ..
  simp [clears,h]

section
variable {X : Type*} [CommRing X] [UniformSpace X] [T2Space X] [IsUniformAddGroup X] [CompleteSpace X]

omit [T2Space X] in
def collect (P : Rep G n) (f : ℕ → X) (S : Pack n) := ∑' i, if ofAddress P.activities i=S then f i else 0

omit [T2Space X] in
lemma access (P : Rep G n) (f : ℕ → X) (h : Summable f) (S : Pack n) :
    Summable (fun i => if ofAddress P.activities i=S then f i else 0) := by
  rw [show (fun i => if ofAddress P.activities i=S then f i else 0) = ({i | ofAddress P.activities i=S} : Set _).indicator f from
    funext fun i => by by_cases e : ofAddress P.activities i=S <;> simp [Set.indicator,e]]
  exact h.indicator _

lemma regroup [ContinuousMul X] (P : Rep G n) (U : Config G n) (f : ℕ → X) (hs : Summable f)
    (ht : Summable fun b : Finset ℕ => if P.activities.admissible P.p U b then ∏ i∈b,f i else 0) :
    (∑' b : Finset ℕ, if P.activities.admissible P.p U b then ∏ i∈b, f i else 0) =
      ∑ S∈ clears (flags P.p.threshold U), ∏ t∈S, collect P f t := by
  have hco : Tendsto Finset.powerset (atTop (α:=Finset ℕ)) atTop := by
    refine tendsto_atTop_atTop.mpr fun L => ⟨L.biUnion id,fun U hu b hb => ?_⟩
    exact Finset.mem_powerset.mpr fun i hi => hu (Finset.mem_biUnion.mpr ⟨b,hb,hi⟩)
  apply tendsto_nhds_unique (ht.hasSum.comp hco)
  let L := clears (flags P.p.threshold U)
  let k := ofAddress P.activities
  have he (S : Finset ℕ) : (∑ b∈S.powerset, if P.activities.admissible P.p U b then ∏ i∈b, f i else 0) =
      ∑ q∈L, ∏ a∈q, ∑ i∈ S, if k i = a then f i else 0 := by
    simp_rw [← Finset.sum_filter]
    rw [fiber_gather]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext b; simp only [Finset.mem_filter]; rw [labeled]
  change Tendsto (fun i : Finset ℕ => ∑ b ∈ i.powerset, if P.activities.admissible P.p U b then ∏ j∈b,f j else 0) (atTop (α:=Finset ℕ)) _
  simp_rw [he]
  refine tendsto_finsetSum L fun i _ => tendsto_finsetProd i fun j _ => (access P f hs j).hasSum
end

end Pack

variable {n : Side} {G : Gauge}

/-- Blank slots in the given alphabet. It also works to reuse such a slot
    with a nonzero vacuum value: they are alternatives, all use that very same
    support and incompatibility, no implicit simultaneous copies. -/
def Room (P : Rep G n) := ∀ q : Pack n, ∃ i : ℕ,
    Pack.ofAddress P.activities i=q ∧ ∀ U, q.zone ∩ flags P.p.threshold U=q.flagsAt → (P.activities.forced i).extraTest U

/-- Actual vacuum on the compressed alphabet. -/
def incumbent (P : Rep G n) (U : Config G n) (q : Pack n) : ℂ :=
    Pack.collect P (fun i => (P.activities.K i U:ℂ)) q

lemma real_book (P : Rep G n) (U : Config G n) {δ κ : ℝ} (h : P.activities.Valid P.p δ κ) :
    (P.activities.gas P.p U:ℂ)=∑ S∈ Pack.clears (flags P.p.threshold U), ∏ t∈S, incumbent P U t := by
  let f i := P.activities.K i U
  have hk : Summable f := by
    obtain ⟨q,H,H'⟩ := Activities.K_total h.boundK
    exact (H.of_nonneg_of_le (fun i => norm_nonneg (f i)) fun i => (H' i).2 U).of_norm
  unfold Activities.gas
  rw [Complex.ofReal_tsum]
  have he (b : Finset ℕ) : (↑(P.activities.gasOccurrence P.p b U):ℂ) =
      if P.activities.admissible P.p U b then ∏ i∈b,(f i:ℂ) else 0 := by
    split_ifs with h <;> simp [h,f,Activities.gasOccurrence]
  simp_rw [he]
  refine Pack.regroup P U (fun i => (f i:ℂ)) (Complex.summable_ofReal.mpr hk) ?_
  simp_rw [← he]
  exact Complex.summable_ofReal.mpr ((Activities.gasSeries h).summable U)
end YM.Multi
