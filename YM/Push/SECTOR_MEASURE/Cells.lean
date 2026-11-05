import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2

/-!
# Actual-sector Borel cells

one oriented step before dropping any defaults.
`Stores.Plot` is a **prerequisite**, not a disjoint partition. For one
allocation, book the actual tolls and wires at the lower thresholds,
with equality default. Record *all* the seeds, physically (including
`RG.flags`, which uses strict `>` and touched sites). This gives exact
disjoint sets, including in the overlap band. These hard cells themselves
make no smoothness claim. A different allocation, E's profile partition of
unity, also fits these prerequisites; see Profile. Both allocations keep
all tag choices (including zero-likelihood ones; the latter make zero
contribution but are not presumed to satisfy Plot).

Measure conventions: two Haar priors as in `StepData`, or the true
free-link `Forest.order` Haar slice and output Haar prior, tags discrete
with *counting* sum (use `likelihood` with that convention). Thus for
sets the joint partition with tag records is on the finite disjoint
union over `S.Choices`: measurability section by section, NO independent
copies of tags for different predictors. Use fixed F; although these
results work for *each* F, the corresponding gauge slices aren't a
partition of full input Haar space.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure

open Lattice RG Wilson Pressure Pressure.Stores Tree MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Enumerate all Stores. No quotienting by overlap of Plots or
identifying different kinds of seed. -/
def inventory (S : StepData c f) : Stores S ≃
    (Finset (Cell f) × Finset (Bond c) × Support c) where
  toFun A := ⟨A.costs, A.aisles, A.flags⟩
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

scoped instance storesFintype : Fintype (Stores S) := Fintype.ofEquiv _ (inventory S).symm

/-- The intact global prerequisites, for a Store listing full typed seed
sets. `Plot` itself only asks the two pairs of implications and the flag
tests locally, and asks *also* that relevant tags have positive frame mass. -/
structure Seeded (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c)
    (x W : ℝ) : Prop where
  fine (p : Cell f) :
    (p ∈ A.costs → fiery G x S.patch.L / 4 ≤ toll U p) ∧
      (p ∉ A.costs → toll U p ≤ fiery G x S.patch.L / 2)
  coarse (b : Bond c) :
    (b ∈ A.aisles → W * fiery G x S.patch.L ≤ wire (S.prediction U k) V b) ∧
      (b ∉ A.aisles → wire (S.prediction U k) V b ≤ 2*W * fiery G x S.patch.L)
  exactFlags : A.flags = RG.flags (temp x) V

/-- Tag support, on the whole physical choices array. -/
def Alive (S : StepData c f) (U : Config G f) (k : S.Choices) := 0 < S.likelihood U k

theorem dead {U : Config G f} {k : S.Choices} (h : ¬ Alive S U k) : S.likelihood U k = 0 :=
  le_antisymm (le_of_not_gt h) (S.likelihood_pos ..)

theorem listed_of_alive {U : Config G f} {k : S.Choices} (h : Alive S U k) (i : Site c) :
    0 < S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) U) (k.1 i) := by
  apply lt_of_le_of_ne ?_ ?_
  · unfold Patch.frameMass
    split <;> positivity
  intro he
  unfold Alive StepData.likelihood at h
  rw [Finset.prod_eq_zero (Finset.mem_univ i) he.symm, zero_mul] at h
  exact (lt_irrefl _) h

theorem Seeded.plot {A : Stores S} {U : Config G f} {V : Config G c} {k : S.Choices} {x W : ℝ}
    (h : Seeded A U k V x W) (hp : Alive S U k) : Plot A U k V x W := by
  refine ⟨fun p _ => h.fine p, fun b _ => h.coarse b, fun i _ => ?_,
    fun i _ => listed_of_alive hp i⟩
  rw [h.exactFlags]

/-- Select the nondefault records strictly above the lower Plot cutoffs;
this *disjointification* of the costs is for measurable partitions, not for
use as smooth profiles or for differentiating across the switch. Defined
also where temperature vanishes. -/
def booking (S : StepData c f) (x W : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :
    Stores S where
  costs := Finset.univ.filter fun p => fiery G x S.patch.L / 4 < toll U p
  aisles := Finset.univ.filter fun b => W*fiery G x S.patch.L < wire (S.prediction U k) V b
  flags := RG.flags (temp x) V

theorem booking_cost {U : Config G f} {k : S.Choices} {V : Config G c} (x W : ℝ) (p) :
    p ∈ (booking S x W U k V).costs ↔ fiery G x S.patch.L / 4 < toll U p := by simp [booking]

theorem booking_aisle {U : Config G f} {k : S.Choices} {V : Config G c} (x W : ℝ) (b) :
    b ∈ (booking S x W U k V).aisles ↔ W*fiery G x S.patch.L < wire (S.prediction U k) V b := by simp [booking]

theorem temp_nonneg (x : ℝ) : 0 ≤ temp x := by unfold temp; positivity

theorem booking_seeded (U : Config G f) (k : S.Choices) (V : Config G c) (x W : ℝ) :
    Seeded (booking S x W U k V) U k V x W := by
  refine ⟨?_, ?_, rfl⟩
  · intro p; rw [booking_cost]; constructor
    · exact le_of_lt
    intro h
    apply (le_of_not_gt h).trans
    have ht : 0 ≤ fiery G x S.patch.L := temp_nonneg _
    linarith
  intro b; rw [booking_aisle]; constructor
  · exact le_of_lt
  intro h
  have he := le_of_not_gt h
  have hn : 0 ≤ wire (S.prediction U k) V b := G.chord_nonneg _
  rw [mul_assoc]
  linarith

section borel

-- These lemmas apply, in particular, with U,V the projections and
-- with U the true drape. Every assertion is at the given common k.
variable {α : Type*} [MeasurableSpace α] {U : α → Config G f} {V : α → Config G c}



theorem toll_meas (p : Cell f) (h : Measurable U) : Measurable (fun a => toll (U a) p) :=
  (show Continuous (fun u : Config G f => toll u p) by unfold toll faceValue; fun_prop).measurable.comp h

theorem wire_meas (k : S.Choices) (b : Bond c) (hb : S.patch.Branches S.kernel G)
    (h : Measurable U) (l : Measurable V) : Measurable (fun a => wire (S.prediction (U a) k) (V a) b) := by
  have hn := (measurable_pi_apply b).comp l
  have he := (measurable_pi_apply b).comp ((S.prediction_meas hb k).comp h)
  unfold wire
  exact (show Continuous G.chord by fun_prop).measurable.comp (hn.mul he.inv)

/-- Every cell of a finite yes/no inventory is measurable. The inventory
needn't omit inconsistent/empty cells. -/
theorem record_meas {ι : Type*} [Fintype ι] {s : α → Finset ι}
    (h : ∀ i, MeasurableSet {a | i ∈ s a}) (l : Finset ι) : MeasurableSet {a | s a = l} := by
  simp only [Finset.ext_iff, Set.setOf_forall]
  refine MeasurableSet.iInter fun i => ?_
  by_cases he : i ∈ l
  · simpa only [he, iff_true] using h i
  simp only [he, iff_false]
  exact (h i).compl

theorem booking_meas (k : S.Choices) (x W : ℝ) (A : Stores S) (hb : S.patch.Branches S.kernel G)
    (h : Measurable U) (l : Measurable V) :
    MeasurableSet {a | booking S x W (U a) k (V a) = A} := by
  have he : ∀ v, v = A ↔ v.costs = A.costs ∧ v.aisles = A.aisles ∧ v.flags = A.flags := by
    intro v
    simpa only [inventory, Equiv.coe_fn_mk, Prod.mk.injEq] using
      (show v = A ↔ inventory S v = inventory S A from (inventory S).injective.eq_iff.symm)
  simp_rw [he, Set.setOf_and]
  refine (record_meas ?_ _).inter ((record_meas ?_ _).inter (l (RG.flags_measurable_eq _ _)))
  · intro i
    simp_rw [booking_cost]
    exact measurableSet_lt measurable_const (toll_meas _ h)
  intro i
  simp_rw [booking_aisle]
  exact measurableSet_lt measurable_const (wire_meas _ _ hb h l)

theorem plot_meas (A : Stores S) (k : S.Choices) (x W : ℝ) (hb : S.patch.Branches S.kernel G)
    (h : Measurable U) (l : Measurable V) : MeasurableSet {a | Plot A (U a) k (V a) x W} := by
  let X := A.dome (5*radiusB x)
  let t := fiery G x S.patch.L
  let M p (a : α) := ¬ Disjoint X (startPos S p) →
    ((p∈A.costs → t/4 ≤ toll (U a) p) ∧ (p∉A.costs → toll (U a) p ≤ t/2))
  let N b (a : α) := ¬ Disjoint X (pinPos b) →
    ((b∈A.aisles → W*t ≤ wire (S.prediction (U a) k) (V a) b) ∧
      (b∉A.aisles → wire (S.prediction (U a) k) (V a) b ≤ 2*W*t))
  let H i (a : α) := i ∈ X → (i ∈ A.flags ↔ i ∈ RG.flags (temp x) (V a))
  let E i (a : α) := i∈X → 0 < S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) (U a)) (k.1 i)
  have hs : {a | Plot A (U a) k (V a) x W} = {a | (∀ i, M i a) ∧ (∀ i,N i a) ∧ (∀ i,H i a) ∧ (∀ i, E i a)} := by
    ext a; exact ⟨fun w => ⟨w.consumes,w.drive,w.precise,w.list⟩,
      fun w => ⟨w.1,w.2.1,w.2.2.1,w.2.2.2⟩⟩
  rw [hs, Set.setOf_and, Set.setOf_and, Set.setOf_and]
  simp only [Set.setOf_forall]
  refine (MeasurableSet.iInter fun i => ?_).inter ((MeasurableSet.iInter fun i => ?_).inter
    ((MeasurableSet.iInter fun i => ?_).inter (MeasurableSet.iInter fun i => ?_)))
  · by_cases e : Disjoint X (startPos S i)
    · simp [M,e]
    by_cases he : i ∈ A.costs
    · simp only [M,e,not_false_eq_true,he,not_true_eq_false,false_implies,and_true,true_implies]
      exact measurableSet_le measurable_const (toll_meas i h)
    simp only [M,e,not_false_eq_true,he,false_implies,true_and,true_implies]
    exact measurableSet_le (toll_meas i h) measurable_const
  · by_cases e : Disjoint X (pinPos i)
    · simp [N,e]
    by_cases he : i ∈ A.aisles
    · simp only [N,e,not_false_eq_true,he,not_true_eq_false,false_implies,and_true,true_implies]
      exact measurableSet_le measurable_const (wire_meas k i hb h l)
    simp only [N,e,not_false_eq_true,he,false_implies,true_and,true_implies]
    exact measurableSet_le (wire_meas k i hb h l) measurable_const
  · by_cases he : i ∈ X
    · have hi : MeasurableSet {a | i ∈ RG.flags (temp x) (V a)} := l (RG.flags_open ..).measurableSet
      by_cases e : i ∈ A.flags
      · simpa only [H, he, e, true_implies, true_iff] using hi
      simp only [H, he, e, true_implies, false_iff]
      exact hi.compl
    simp [H,he]
  by_cases he : i ∈ X
  · simp only [E, he, true_implies]
    apply measurableSet_lt measurable_const
    exact ((S.patch.frameMass_meas _).comp (show Continuous (fun u : Config G f =>
      expandAt (S.ratio.embed i) u) by unfold expandAt; fun_prop).measurable).comp h
  simp [E,he]

end borel













theorem slice_drape (F : Forest S.ratio) (U : Config G f) :
    SliceSet S F U ↔ ∃! a : F.Slice G, F.drape a = U := by
  constructor
  · intro h
    let a : F.Slice G := fun i => U i
    refine ⟨a, funext fun i => ?_, fun b hb => ?_⟩
    · by_cases he : i ∈ F.trunks
      · exact (F.on_tree a ⟨i,he⟩).trans (h i he).symm
      exact F.off_tree a ⟨i,he⟩
    funext i
    exact (F.off_tree b i).symm.trans (congr_fun hb i)
  rintro ⟨a,rfl,-⟩ i hi
  exact F.on_tree a ⟨i,hi⟩


















end YM.Push.SectorMeasure
