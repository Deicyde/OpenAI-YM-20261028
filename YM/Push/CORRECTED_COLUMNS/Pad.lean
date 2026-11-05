import YM.Push.CORRECTED_COLUMNS.Rendezvous
/-!
# Pad the shared comparison vacuum dictionary

Join labels need not be preexisting! Here do this on the selected
last-stretch representations without changing a single density (as
opposed to silently assuming vacancies in the *original* C.path).
Adds arbitrarily many symmetric null addresses, even tests/moves/budgets
preserved. Need of course preserve this scope in subsequent operations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Pad
open Set MeasureTheory Function Lattice Wilson RG Marker
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} (P : Rep G n)

/-- include *all* shapes, 'even if no representation has the tag.
`extraTest` true; subsequent payload carries the additional conditions. -/
abbrev Shape (n : Side) := {p : Support n × Support n // p.2.Nonempty ∧ p.2 ⊆ p.1}

private lemma codes (n : Side) : Nonempty (Denumerable (ℕ ⊕ (Shape n × ℕ))) := by
  let Q : Shape n := ⟨({(0:Site n)},{0}),by simp⟩
  haveI : Nonempty (Shape n) := ⟨Q⟩
  exact nonempty_denumerable _

def number (n : Side) : ℕ ⊕ (Shape n × ℕ) ≃ ℕ := @Denumerable.eqv _ (Classical.choice (codes n))
def original (n : Side) (i : ℕ) := number n (Sum.inl i)
def slot (p : Shape n) (i : ℕ) := number n (Sum.inr (p,i))
lemma original_inj (n : Side) : Injective (original n) := fun _ _ h => Sum.inl.inj ((number n).injective h)
def origin (P : Rep G n) : ℕ → ForcedAddress G n := P.activities.forced
def zeroed (G : Gauge) (p : Shape n) : ForcedAddress G n := ⟨p.val.1,p.val.2,p.property.1,p.property.2,fun _=>True⟩

def enlarge (P : Rep G n) : Rep G n :=
    { P with activities :=
        { P.activities with forced := Sum.elim (origin P) (fun v => zeroed G v.1) ∘ (number n).symm
                            K := Sum.elim P.activities.K (fun _ => fun _ => 0) ∘ (number n).symm } }
lemma same (i) : (enlarge P).activities.forced (original n i)=P.activities.forced i := by
  unfold enlarge original; simp [origin]
lemma subject (i) : (enlarge P).activities.K (original n i)=P.activities.K i := by unfold enlarge original; simp
lemma empty (q : Shape n) (i) : (enlarge P).activities.forced (slot q i)=zeroed G q := by unfold enlarge slot; simp
lemma emptyK (q : Shape n) (i) : (enlarge P).activities.K (slot q i)=0 := by unfold enlarge slot; simp; rfl
lemma casesTag (i : ℕ) : (∃ j, i=original n j) ∨ ∃  (p : Shape n) (j : ℕ), i=slot p j := by
  obtain ⟨k,h⟩ := (number n).surjective i
  cases k with
  | inl j => exact Or.inl ⟨j,h.symm⟩
  | inr j => exact Or.inr ⟨j.1,j.2,h.symm⟩

lemma new_shape (p : Rep G n) (q : Shape n) i :
    claims (enlarge p) (slot q i)=q.val.2 ∧ oldSites (enlarge p) (slot q i)=q.val.1 := by unfold claims oldSites; rw [empty]; exact ⟨rfl,rfl⟩
lemma old_shape (p : Rep G n) i :
    claims (enlarge p) (original n i)=claims p i ∧ oldSites (enlarge p) (original n i)=oldSites p i := by unfold claims oldSites; rw [same]; exact ⟨rfl,rfl⟩

section
-- transport budgets through any tag injection
variable {V A : Type*} (f : V → A) (h : Injective f)

lemma inclusive {M : Finset A} [DecidableEq A] (H : ∀ i∈M,i∈Set.range f) :∃ D : Finset V,D.image f = M := by
  classical
  induction M using Finset.induction_on with
  | empty => exact ⟨∅,Finset.image_empty _⟩
  | @insert i s hi ih =>
    obtain ⟨D,hD⟩ := ih (fun i hi => H i (Finset.mem_insert_of_mem hi))
    obtain ⟨w,hw⟩ := H i (Finset.mem_insert_self ..)
    exact ⟨insert w D, by rw [Finset.image_insert,hD,hw]⟩
include h
lemma sums {B : Type*} [AddCommMonoid B] [TopologicalSpace B] (u : V → B) (v : A → B) (ha : ∀ i,v (f i)=u i)
    (he : Function.support v⊆Set.range f) : (∑' i,u i)=∑' i,v i := by
  simp_rw [← h.tsum_eq he,ha]
lemma absolute {u : V → ℝ} {v : A → ℝ} {C : ℝ} (ha : ∀ i,v (f i)=u i)
    (he : Function.support v⊆Set.range f) (hh : SumBudget u C) : SumBudget v C := by
  constructor
  · intro i; by_cases hi : v i=0
    · rw [hi]
    obtain ⟨k,rfl⟩ := he (show v i ≠ 0 from hi); rw [ha]; exact hh.1 k
  rw [← h.summable_iff (fun i hi => by_contra fun w => hi (he w)),← sums f h u v ha he,show v ∘ f = u from funext ha]
  exact hh.2
end

section






-- all evaluations use Constraint eligibility even for zero payloads;
-- correspondence of constrained old families.
lemma trans (U : Config G n) (X : Finset ℕ) :
    (enlarge P).activities.admissible (enlarge P).p U (X.image (original n)) ↔ P.activities.admissible P.p U X := by
  have he : (X.image (original n)).biUnion (fun i => ((enlarge P).activities.forced i).inventory)=X.biUnion (claims P) := by
    ext; simp [same,claims]
  unfold Activities.admissible; rw [he]
  apply and_congr_left
  intro h; constructor
  · intro hf i hi j hj hh
    have ht : Disjoint (oldSites (enlarge P) (original n i)) (oldSites (enlarge P) (original n j)) :=
      hf (Finset.mem_image_of_mem _ hi) (Finset.mem_image_of_mem _ hj) ((original_inj n).ne hh)
    rw [(old_shape P i).2,(old_shape P j).2] at ht; exact ht
  intro hf i hi j hj hu; obtain ⟨i,hiA,rfl⟩ := Finset.mem_image.mp hi; obtain ⟨j,hjA,rfl⟩ := Finset.mem_image.mp hj
  rw [same,same]; exact hf hiA hjA (fun w => hu (congr_arg _ w))
lemma unchanged (U) : (enlarge P).eval U=P.eval U := by
  unfold Rep.eval
  apply congr_arg (fun v : ℝ => Real.exp (P.exponent U)*v)
  apply Eq.symm
  refine sums (Finset.image (original n)) (Finset.image_injective (original_inj n)) _
    (fun i => (enlarge P).activities.gasOccurrence (enlarge P).p i U) ?_ ?_
  · intro i; unfold Activities.gasOccurrence; split_ifs with he he' he'
    · rw [Finset.prod_image (original_inj n).injOn]; simp only [subject]
    · exact (he' ((trans P ..).1 he)).elim
    · exact (he ((trans P U i).2 he')).elim
    rfl
  intro i hi; apply inclusive
  intro j hj; rcases casesTag (n:=n) j with ⟨v,rfl⟩|⟨p,j,rfl⟩
  · exact ⟨v,rfl⟩
  exfalso; apply hi; unfold Activities.gasOccurrence; dsimp only; split
  · exact Finset.prod_eq_zero hj (by rw [emptyK]; rfl)
  rfl
end
end YM.Push.Corrected.Pad
