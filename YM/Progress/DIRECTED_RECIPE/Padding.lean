import YM.Ac.Table
import YM.Pressure.Seeds

/-!
# Adding addresses

Generic dictionary embedding on the unmarked population. Raw incidences and even
pre-mask E values are preserved on the image. Support is not inferred from what
function the coefficient happens to be. `admits` permits putting additional tests
*inside* the K coefficients (so these still enforce them, including if transported;
keep the original activities too if needing the named predicates). It does not
allow changing disjointness or coverage. Beware that to acquire Valid in the
target this alone does NOT pay the new tests or covariance on *all* the addresses!

Used downstream on the same maps before and after varying coupling. All sums
indexed by actual labels. The tsum equality lemmas also work as reindexings on
bare `tsum`; use the budget lemmas / Valid in conjunction to have genuine sums.
No new polymer bound asserted for the incoming labels.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe

open Function Set RG  Wilson Lattice MeasureTheory RG.Shoot
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

section Basic
variable {ι κ : Type*} (t : ι ↪ κ)

def stuff {V : Type*} [Zero V] (f : ι → V) (j : κ) := extend t f (fun _ => 0) j

lemma stuffed {V : Type*} [Zero V] (f : ι → V) (i : ι) : stuff t f (t i) = f i :=
  t.injective.extend_apply ..

lemma blank {V : Type*} [Zero V] (f : ι → V) {j : κ} (h : j ∉ Set.range t) : stuff t f j = 0 :=
  extend_apply' _ _ _ h

lemma transferred_sum {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    {f : κ → V} {g : ι → V} (hf : ∀ i, f (t i) = g i) (h : ∀ j ∉ range t, f j = 0) :
    ∑' j, f j = ∑' i, g i := by
  rw [← t.injective.tsum_eq, funext hf]
  intro j hj
  contrapose! hj
  simpa [Function.support] using h j hj

lemma transferred_summable {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    {f : κ → V} {g : ι → V} (hf : ∀ i, f (t i) = g i) (h : ∀ j ∉ range t, f j = 0) :
    Summable f ↔ Summable g := by
  rw [← t.injective.summable_iff h, show f ∘ t = g from funext hf]

lemma transfer_budget {f : κ → ℝ} {g : ι → ℝ} (hf : ∀ i, f (t i) = g i)
    (h : ∀ j ∉ range t, f j = 0) {C : ℝ} (hg : SumBudget g C) : SumBudget f C := by
  refine ⟨fun j => ?_, (transferred_summable t hf h).2 hg.2.1, (transferred_sum t hf h).trans_le hg.2.2⟩
  by_cases H : j ∈ range t
  · obtain ⟨i,rfl⟩ := H
    rw [hf]; exact hg.1 i
  rw [h j H]

lemma finsets_full (t : ι ↪ κ) (a : Finset κ) (h : ∀ i∈a, i ∈ range t) :
    a ∈ range (Finset.map t) := by
  classical
  induction a using Finset.induction_on with
  | empty => exact ⟨∅, rfl⟩
  | insert j a hj ih =>
    obtain ⟨i,rfl⟩ := h j (Finset.mem_insert_self _ _)
    obtain ⟨a,rfl⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨insert i a, Finset.map_insert ..⟩

/-- In a packet off the old index range at least one slot didn't exist before. -/
lemma finsets_off (a : Finset κ) (h : a ∉ range (Finset.map t)) :
    ∃ i∈a, i ∉ range t := by
  by_contra! he
  exact h (finsets_full _ _ he)

lemma transferred_packets {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    {f : Finset κ → V} {g : Finset ι → V} (hf : ∀ i, f (i.map t) = g i)
    (h : ∀ j, ∀ k∈j, k ∉ range t → f j = 0) :
    ∑' j, f j = ∑' i, g i := by
  refine transferred_sum ⟨Finset.map t, Finset.map_injective t⟩ hf (fun i hi => ?_)
  obtain ⟨j,hj,hj'⟩ := finsets_off t i hi
  exact h i j hj hj'

lemma mapped_biUnion {s : Type*} [DecidableEq s] {f : κ → Finset s} {g : ι → Finset s}
    (hf : ∀ i, f (t i) = g i) (a : Finset ι) : (a.map t).biUnion f = a.biUnion g := by
  ext x; constructor <;> intro h
  · obtain ⟨j,hj,h⟩ := Finset.mem_biUnion.mp h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_biUnion.mpr ⟨_,hi,hf i ▸ h⟩
  obtain ⟨j,hj,h⟩ := Finset.mem_biUnion.mp h
  exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_map.mpr ⟨j,hj,rfl⟩, (hf j).symm ▸ h⟩

lemma paired {R : κ → κ → Prop} {Q : ι → ι → Prop} (hx : ∀ a b, R (t a) (t b) ↔ Q a b)
    (a : Finset ι) : ((a.map t : Finset κ) : Set κ).Pairwise R ↔ (a : Set ι).Pairwise Q := by
  rw [Finset.coe_map]
  constructor
  · intro h i hi j hj hn
    exact (hx i j).1 (h (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) (t.injective.ne hn))
  rintro h _ ⟨i,hi,rfl⟩ _ ⟨j,hj,rfl⟩ hn
  exact (hx i j).2 (h hi hj (ne_of_apply_ne t hn))
end Basic

section Zero
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G : Gauge} {n : Side}

lemma lefts_zero (l : List (Directions G n)) (U : Config G n) :
    leftDerivs (0 : Config G n → X) l U = 0 := by
  induction l generalizing U with
  | nil => rfl
  | cons d l ih => simp [leftDerivs,ih]

lemma no_cost (P : BudgetPoint) (o : Site n) (L : Support n) :
    P.supBounds o L (0 : Config G n → X) 0 := by
  refine ⟨le_rfl,fun U _ l _ _ => ?_⟩; simp only [lefts_zero, norm_zero, le_refl]

lemma unspent (P : BudgetPoint) (L : Support n) [MeasurableSpace X] :
    P.Regular L (0 : Config G n → X) := by
  refine ⟨fun _ _ _ => rfl, measurable_const, fun _ _ => rfl, fun _ _ => contDiffAt_const, ?_⟩
  intro U h A l hl
  simp only [lefts_zero]; exact hasDerivAt_const _ _
end Zero

variable {G : Gauge} {n : Side} {δ w : ℝ} {P : BudgetPoint}

/-- Reindexing on represented species. Old predicates still at A and on every
numerical read. Permit extra internal tests there; don't allow weakening
footprints by such renormalization. Later consumers, e.g. if estimating old K
on the putative larger eligibility set in B: must keep A and use its real
`ForcedFamily`, not merely infer that the old test passed. -/
structure Readdress (P : BudgetPoint) (e k : ℕ ↪ ℕ) (A B : Activities G n) : Prop where
  same_reg i : B.reg (e i) = A.reg i
  sup i : (B.forced (k i)).support = (A.forced i).support
  inv i : (B.forced (k i)).inventory = (A.forced i).inventory
  emits i : B.E (e i) = A.E i
  kernels i : B.K (k i) = A.K i
  restE i : i ∉ range e → B.E i = 0
  restK i : i ∉ range k → B.K i = 0
  admits i U : (A.forced i).eligible P.threshold U → (B.forced (k i)).eligible P.threshold U

namespace Readdress
variable {A B A' B' : Activities G n} {e k : ℕ ↪ ℕ} (h : Readdress P e k A B)
include h

lemma old_permit (he : A.ForcedFamily P) (i : ℕ) (U : Config G n) (hu : B.K (k i) U ≠ 0) :
    (A.forced i).eligible P.threshold U := by
  rw [h.kernels] at hu
  exact he.permit i U hu

lemma covers (U : Config G n) (b : Finset ℕ) :
    B.admissible P U (b.map k) ↔ A.admissible P U b := by
  unfold Activities.admissible
  rw [paired k (Q:=fun i j => Disjoint (A.forced i).support (A.forced j).support)
    (fun a b => by rw [h.sup,h.sup]), mapped_biUnion k h.inv]

lemma same_gasOccurrence (U : Config G n) (b : Finset ℕ) :
    B.gasOccurrence P (b.map k) U = A.gasOccurrence P b U := by
  classical
  by_cases H : A.admissible P U b
  · simp only [Activities.gasOccurrence, H, h.covers, ↓reduceIte, Finset.prod_map, h.kernels]
  simp only [Activities.gasOccurrence, H, h.covers, ↓reduceIte]

lemma same_gas : B.gas P = A.gas P := by
  funext U
  refine transferred_packets k (h.same_gasOccurrence U) (fun b i hi h0 => ?_)
  unfold Activities.gasOccurrence; split
  · exact Finset.prod_eq_zero hi (by rw [h.restK _ h0]; rfl)
  rfl

lemma same_sum : B.additive P = A.additive P := by
  funext U
  refine transferred_sum e (fun i => ?_) (fun i hi => ?_)
  · unfold Activities.regularOccurrence; rw [h.same_reg,h.emits]
  unfold Activities.regularOccurrence; rw [h.restE _ hi]; simp [masked,Set.indicator]

lemma Ebound (hg : A.EBound P δ) : B.EBound P δ := by
  obtain ⟨b,hb,H⟩ := hg
  refine ⟨stuff e b, fun i => ?_, fun x => transfer_budget e ?_ ?_ (H x)⟩
  · by_cases hi : i ∈ range e
    · obtain ⟨i, rfl⟩ := hi
      rw [h.same_reg,h.emits, stuffed]; exact hb _
    rw [h.restE i hi, blank _ _ hi]; exact no_cost ..
  · simp only [h.same_reg, stuffed, implies_true]
  intro j hj; simp [blank _ _ hj, BudgetPoint.mass]

lemma Kbound (hg : A.KBound P w) : B.KBound P w := by
  obtain ⟨b,hb,H⟩ := hg
  refine ⟨stuff k b, fun i => ?_, fun x => transfer_budget k ?_ ?_ (H x)⟩
  · by_cases hi : i ∈ range k
    · obtain ⟨i,rfl⟩ := hi
      rw [h.kernels, stuffed]; exact hb _
    simp [h.restK i hi, blank _ _ hi]
  · simp only [h.sup, stuffed, implies_true]
  intro j hj; simp [blank _ _ hj, BudgetPoint.mass]

lemma regular (hg : A.RegularFamily P) : B.RegularFamily P := by
  constructor
  · intro i; by_cases hi : i ∈ range e
    · obtain ⟨i,rfl⟩ := hi
      rw [h.same_reg,h.emits]; exact hg.smooth i
    rw [h.restE _ hi]; exact unspent ..
  · intro i; by_cases hi : i ∈ range e
    · obtain ⟨i,rfl⟩ := hi
      rw [h.emits, hg.at_flat]
    rw [h.restE _ hi]; rfl
  intro i; by_cases hi : i ∈ range e
  · obtain ⟨i,rfl⟩ := hi
    rw [h.same_reg,h.emits]; exact hg.vanish i
  intro hx x y h1 h2
  rw [h.restE _ hi]; unfold logHessian
  rw [show (fun q : Directions G n => (0 : Config G n → ℝ) (increment 1 q)) = (fun _ => (0:ℝ)) from rfl,
    iteratedFDeriv_const_of_ne (by norm_num : (2:ℕ) ≠ 0)]; rfl

lemma forced_family (hg : A.ForcedFamily P)
    (he : ∀ i t U, (B.forced i).extraTest (gauge t U) ↔ (B.forced i).extraTest U)
    (hT : ∀ i, MeasurableSet {U | (B.forced i).extraTest U})
    (hu : ∀ i, UsesFinal P.threshold (B.forced i).support (B.forced i).extraTest) :
    B.ForcedFamily P := by
  refine ⟨fun i => ?_, he, fun i => ?_, hT, fun i => ?_, hu, fun i => ?_⟩
  all_goals by_cases hi : i ∈ range k
  · obtain ⟨j,rfl⟩ := hi
    rw [h.kernels]; exact hg.sym j
  · rw [h.restK i hi]; exact fun _ _ => rfl
  · obtain ⟨j,rfl⟩ := hi
    rw [h.kernels]; exact hg.meas j
  · rw [h.restK i hi]; exact measurable_const
  · obtain ⟨j,rfl⟩ := hi
    rw [h.kernels,h.sup]; exact hg.reads j
  · rw [h.restK i hi]; exact fun _ _ _ _ => rfl
  · obtain ⟨j,rfl⟩ := hi
    exact fun x hx => h.admits j x (h.old_permit hg j x hx)
  simp [h.restK _ hi]

lemma compares (h' : Readdress P e k A' B') {w : ℝ} (hx : deviation P A A' w) : deviation P B B' w := by
  obtain ⟨c,d,hc,hd,hce,hdk⟩ := hx
  refine ⟨stuff e c,stuff k d,fun i => ?_, fun i => ?_,transfer_budget e ?_ ?_ hce, transfer_budget k ?_ ?_ hdk⟩
  · by_cases H : i ∈ range e
    · obtain ⟨j,rfl⟩ := H
      rw [h.same_reg,h.emits,h'.emits,stuffed]; exact hc j
    rw [h.restE _ H,h'.restE _ H,blank _ _ H]
    exact ⟨le_rfl, fun U _ l _ _ => by simp⟩
  · by_cases H : i ∈ range k
    · obtain ⟨j,rfl⟩ := H
      rw [h.kernels,h'.kernels,stuffed]; exact hd j
    simp only [h.restK _ H,h'.restK _ H,blank _ _ H, le_refl,sub_self, norm_zero,
      implies_true, and_self]
  · simp [h.same_reg,stuffed]
  · intro j hj; simp [blank _ _ hj, BudgetPoint.mass]
  · simp [h.sup,stuffed]
  intro j hj; simp [blank _ _ hj, BudgetPoint.mass]
end Readdress
end YM.Progress.DirectedRecipe
