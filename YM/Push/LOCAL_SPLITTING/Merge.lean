import YM.Push.LOCAL_SPLITTING.Atoms
import YM.Push.LOCAL_SPLITTING.Budget

/-!
# Multiplying flag-requiring attachments into the specified activity system

E `Jmdef` forced side at singleton-marker order. Use a reservation in the
*same* alphabet as for the vacuum. The old K terms at these addresses do NOT
even need to be zero, but their addresses (supports/inventories/tests) must
already permit the bundle uses below; just an arbitrary KBound doesn't give
this. No support re-fitting after seeing amplitudes or flags. This file does
structure and absolute budgets; evaluation bijection in the sequel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side} {ι : Type*}

abbrev patch (A : Activities G n) (i : ℕ) := (A.forced i).support
abbrev flagsFor (A : Activities G n) (i : ℕ) := (A.forced i).inventory
abbrev Separate (A : Activities G n) (q : Finset ℕ) := (q : Set ℕ).PairwiseDisjoint (patch A)

structure Packs (A : Activities G n) (X : Support n) (q : Finset ℕ) : Prop where
  nonempty : q.Nonempty
  separate : Separate A q
  hits : ∀ j∈q, ¬ Disjoint X (patch A j)

abbrev Pack (A : Activities G n) (X : Support n) := {q // Packs A X q}
/-- Remember the donor occurrence. -/
abbrev Letters (A : Activities G n) (X : ι → Support n) := Σ i : ι, Pack A (X i)

namespace Letters
variable {A : Activities G n} {X : ι → Support n}

abbrev bundle (s : Letters A X) : Finset ℕ := s.2.val

def total (s : Letters A X) := X s.1 ∪ s.bundle.biUnion (patch A)
def keeps (s : Letters A X) := s.bundle.biUnion (flagsFor A)

theorem keeps_ne (s : Letters A X) : s.keeps.Nonempty := by
  obtain ⟨j,hj⟩ := s.2.property.nonempty
  exact (A.forced j).inventory_ne.mono (Finset.subset_biUnion_of_mem (flagsFor A) hj)

theorem keeps_sub (s : Letters A X) : s.keeps ⊆ s.total := fun _ hx => by
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,(A.forced i).inventory_sup hx⟩)

theorem contains (s : Letters A X) {j : ℕ} (h : j∈s.bundle) : patch A j ⊆ s.total :=
  (Finset.subset_biUnion_of_mem (patch A) h).trans Finset.subset_union_right
end Letters

/-- Dormant-address prerequisite to fix BEFORE vacuum continuation (or pay
via equivalent inventories retained there). Does not assume any estimates
on source or output. Old extra tests occur in the product of original
activities; use the extraTest=True slots to avoid imposing new predicates. -/
structure Slots (A : Activities G n) (X : ι → Support n) where
  label : Letters A X ↪ ℕ
  support (s) : patch A (label s) = s.total
  inventory (s) : flagsFor A (label s) = s.keeps
  allows (s) (U : Config G n) : (A.forced (label s)).extraTest U

structure ForceFormat (B : BudgetPoint) (A : Activities G n) (o : Site n) (f : ℕ → Config G n → ℂ) : Prop where
  forcing (i : ℕ) (U : Config G n) : f i U ≠ 0 → (A.forced i).eligible B.threshold U
  carried (i : ℕ) : f i ≠ 0 → o ∈ patch A i
  invariant (i : ℕ) : GaugeInvariant (f i)
  supported (i : ℕ) : UsesFinal B.threshold (patch A i) (f i)
  borel (i : ℕ) : Measurable (f i)

def ForceCost (B : BudgetPoint) (A : Activities G n) (f : ℕ → Config G n → ℂ) (c : ℝ) :=
  ∃ e : ℕ → ℝ, SumBudget (fun i => B.mass (patch A i) (e i)) c ∧ ∀ i, 0 ≤ e i ∧ ∀ U, ‖f i U‖ ≤ e i

section Add
variable {B : BudgetPoint} {A : Activities G n} {f g : ℕ → Config G n → ℂ} {a b : ℝ} {o : Site n}





theorem ForceFormat.add (hf : ForceFormat B A o f) (hg : ForceFormat B A o g) : ForceFormat B A o (f+g) := by
  refine ⟨fun i U hu => ?_,fun i hi => ?_,fun i g U => congr_arg₂ (·+·) (hf.invariant i g U) (hg.invariant i g U),
    fun i U V huv ht => congr_arg₂ (·+·) (hf.supported i U V huv ht) (hg.supported i U V huv ht),fun i => (hf.borel i).add (hg.borel i)⟩
  · by_contra he
    simp [not_not.mp (mt (hf.forcing i U) he),not_not.mp (mt (hg.forcing i U) he)] at hu
  by_contra he
  simp [not_not.mp (mt (hf.carried i) he),not_not.mp (mt (hg.carried i) he)] at hi

theorem ForceCost.add (hf : ForceCost B A f a) (hg : ForceCost B A g b) : ForceCost B A (f+g) (a+b) := by
  obtain ⟨e,hE,h⟩ := hf; obtain ⟨u,hU,q⟩ := hg
  exact ⟨e+u,by simpa [BudgetPoint.mass, mul_add] using sumBudget_add hE hU,fun i => ⟨add_nonneg (h i).1 (q i).1, fun U => (norm_add_le ..).trans (add_le_add ((h i).2 U) ((q i).2 U))⟩⟩
end Add

namespace Slots
variable {A : Activities G n} {X : ι → Support n} (S : Slots A X)

open scoped Classical in
def payload (t : ℝ) (s : Letters A X) (f : ι → Config G n → ℂ) (U : Config G n) :=
  if (A.forced (S.label s)).eligible t U then f s.1 U * ∏ j ∈ s.bundle, (A.K j U : ℂ) else 0

def pack (t : ℝ) (f : ι → Config G n → ℂ) : ℕ → Config G n → ℂ := extend S.label (fun s => S.payload t s f) 0

@[simp] theorem pack_label (t : ℝ) (f : ι → Config G n → ℂ) (s : Letters A X) :
    S.pack t f (S.label s) = S.payload t s f := S.label.injective.extend_apply ..

theorem pack_none (t : ℝ) (f : ι → Config G n → ℂ) (j : ℕ) (h : ¬∃ i, S.label i = j) :
    S.pack t f j = 0 := Function.extend_apply' _ _ _ h

def packLinear (t : ℝ) : (ι → Config G n → ℂ) →ₗ[ℂ] ℕ → Config G n → ℂ where
  toFun := S.pack t
  map_add' f g := by
    funext j U; by_cases hx : ∃ i, S.label i = j
    · obtain ⟨i,rfl⟩ := hx; simp only [Pi.add_apply,pack_label,payload]; split <;> simp [add_mul]
    simp [pack_none _ _ _ _ hx]
  map_smul' f g := by
    funext j U; by_cases hx : ∃ i, S.label i = j
    · obtain ⟨i,rfl⟩ := hx; simp only [Pi.smul_apply,pack_label,payload,RingHom.id_apply,smul_eq_mul]; split <;> simp [mul_assoc]
    simp [pack_none _ _ _ _ hx]

theorem forceFormat {B : BudgetPoint} {o : Site n} {f : ι → Config G n → ℂ} (ha : A.ForcedFamily B)
    (ho : ∀ i, o∈X i) (hf : ∀ i, Attaches B.threshold (X i) (f i)) : ForceFormat B A o (S.pack B.threshold f) := by
  classical
  refine ⟨fun i U hu => ?_,fun i hi => ?_,fun i => ?_,fun i => ?_,fun i => ?_⟩ <;> by_cases hx : ∃ s, S.label s = i
  all_goals (first | obtain ⟨s,rfl⟩ := hx | simp [S.pack_none _ _ _ hx] at * )
  · by_contra he
    simp [payload,he] at hu
  · exact S.support _ ▸ Finset.mem_union_left _ (ho _)
  · intro g U; rw [pack_label]; unfold payload
    simp only [(Work.H03.eligible_gauge _ _ _ _ (ha.symtest _ g U)),(hf s.1).symmetry g U,fun j => ha.sym j g U]
  · intro g U; rfl
  · rw [pack_label]; intro U V huv ht
    unfold payload; rw [Work.H03.eligible_reads _ _ (ha.reads_test _) U V huv ht]
    rw [show patch A (S.label s) = s.total from S.support _] at huv ht
    split
    · rw [Work.H03.reads_larger (Finset.subset_union_left (s₂:=s.bundle.biUnion (patch A))) (hf _).sites U V huv ht]; congr 1
      exact Finset.prod_congr rfl fun j hj => congr_arg Complex.ofReal (Work.H03.reads_larger (s.contains hj) (ha.reads j) U V huv ht)
    rfl
  · intro U V _ _; rfl
  · rw [pack_label]; unfold payload
    exact Measurable.ite (Work.H03.eligible_measurable _ _ (ha.meas_test _)) ((hf _).borel.mul
      (Finset.measurable_fun_prod _ fun i _ => Complex.continuous_ofReal.measurable.comp (ha.meas i))) measurable_const
  · exact measurable_const

end Slots

def mergePrice (B : BudgetPoint) (w : ℝ) (X : Support n) (a : ℝ) := B.mass X a * (Real.exp ((X.card:ℝ)*w) - 1)

theorem mergePrice_nonneg (B : BudgetPoint) {w a : ℝ} (X : Support n) (hw : 0 ≤ w) (ha : 0 ≤ a) : 0 ≤ mergePrice B w X a :=
  mul_nonneg (ha.trans (B.loMass X a ha)) (sub_nonneg.mpr (Real.one_le_exp (by positivity)))

section Budget
variable {B : BudgetPoint} {A : Activities G n} {X : ι → Support n}

theorem packBudget (X : Support n) {a : ℝ} {b : ℕ → ℝ} (ha : 0 ≤ a) {w : ℝ}
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ x : Site n, SumBudget (fun i => if x ∈ patch A i then B.mass (patch A i) (b i) else 0) w) :
    SumBudget (fun s : Pack A X => B.mass (X∪s.val.biUnion (patch A)) (a * ∏ j ∈ s.val, b j)) (mergePrice B w X a) := by
  classical
  let y (i : ℕ) := if Disjoint X (patch A i) then 0 else B.mass (patch A i) (b i)
  have he : SumBudget y ((X.card:ℝ)*w) := sumBudget_meeting X (fun i => (hb i).trans (B.loMass _ _ (hb i))) hc
  let prod' (s : Finset ℕ) := if s.Nonempty then ∏ i∈s, y i else 0
  refine sumBudget_mono (sumBudget_mul_left (sumBudget_subtype (Packs A X) (a:=prod') (sumBudget_exponential he)) (ha.trans (B.loMass X a ha))) (fun i => mul_nonneg (Real.exp_pos _).le (mul_nonneg ha (Finset.prod_nonneg fun j _ => hb j))) (fun s => ?_) le_rfl
  dsimp only [prod']; rw [if_pos s.property.nonempty]
  convert mass_union_meeting X (patch A) s.val s.property.hits b a (fun j _ => hb j) ha B using 1
  congr 1; exact Finset.prod_congr rfl fun i hi => if_neg (s.property.hits i hi)

theorem Slots.forceCost (S : Slots A X) {a : ι → ℝ} {c w : ℝ} {f : ι → Config G n → ℂ} (hw : A.KBound B w)
    (h : SumBudget (fun i => mergePrice B w (X i) (a i)) c) (hp : ∀ i, 0 ≤ a i) (hf : ∀ i U, ‖f i U‖ ≤ a i) :
    ForceCost B A (S.pack B.threshold f) c := by
  obtain ⟨b,hb,h'⟩ := hw
  let p (s : Letters A X) := a s.1 * ∏ i∈s.bundle, b i
  have h0 (s) : 0 ≤ p s := mul_nonneg (hp _) (Finset.prod_nonneg fun i _ => (hb i).1)
  let e := Function.extend S.label p (0 : ℕ → ℝ)
  refine ⟨e, sumBudget_pass S.label _ (sumBudget_sigma (fun i => ?_) h) ?_,fun i => ?_⟩
  · simpa only [e, S.label.injective.extend_apply, S.support,Letters.total,p] using! packBudget (A:=A) (B:=B) (X i) (hp i) (fun i => (hb i).1) h'
  · intro i hi; rw [show e i = 0 from extend_apply' _ _ _ hi, BudgetPoint.mass, mul_zero]
  by_cases hi : ∃ s, S.label s = i
  · obtain ⟨s,rfl⟩ := hi
    rw [show e _ = p s from S.label.injective.extend_apply ..,S.pack_label]
    refine ⟨h0 s, fun U => ?_⟩; unfold payload; split
    · rw [norm_mul,norm_prod]; refine mul_le_mul (hf ..) ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) (hp _)
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => by simpa using (hb i).2 U
    rw [norm_zero]; exact h0 _
  rw [show e i = 0 from extend_apply' _ _ _ hi,S.pack_none _ _ _ hi]; simp
end Budget
end YM.Push.Local
