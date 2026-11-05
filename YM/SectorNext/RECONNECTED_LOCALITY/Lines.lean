import YM.SectorNext.RECONNECTED_LOCALITY.Brochures
import YM.Work.A05
import YM.Work.C22
import YM.Work.F02.Path


set_option warningAsError false

/-!
# Last encoding to ℕ (with explicit forced reserve slots)

Need `Activities` true support invariants even at dormant labels, compulsory
nonempty inventory for every index & coherent H/translation on ALL indices.
Doesn't assert that number or type of blanks will suffice to run later transfers;
choose more here where needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
open RG Wilson Lattice Filter Function Ledger Finset MeasureTheory
open scoped Classical

variable {G : Gauge} {c : Side} {ι β : Type*}

structure Room (G : Gauge) (c : Side) (ι : Type*) where
  reg : ι → RegularAddress c
  ink : ι → Config G c → ℝ

namespace Room

variable (R : Room G c ι)

abbrev spot (i : ι) := (R.reg i).site
abbrev range (i : ι) := (R.reg i).support

structure Plan (s : Signed) (b : Site c) where
  letter : Equiv.Perm ι
  site i : R.spot (letter i)=affine s b (R.spot i)
  shape : carrying letter (sitePerm s b) R.range R.range
  symm i V : R.ink (letter i) V=R.ink i (pull s b V)

structure Names (P : BudgetPoint) : Prop where
  regular i : P.Regular (R.range i) (R.ink i)
  flat i : R.ink i 1=0
  fiber i : Nonwrapping (R.range i) (R.spot i) → ∀ a b,
    IsAffineDirection (R.spot i) a → IsAffineDirection (R.spot i) b → logHessian (R.ink i) a b=0
  respects s b : Nonempty (R.Plan s b)



variable (D : Brand G c β)

/-- regular reserve: infinite even if R indexed by empty set. -/
abbrev Cipher (c : Side) := Site c × ℕ

/-- forced reserve includes every nonempty inventory/support.
No internal predicate on these padding slots. -/
abbrev CipherK (c : Side) := {s : Support c × Support c × ℕ // s.2.1.Nonempty ∧ s.2.1 ⊆ s.1}



variable (q : ℕ ≃ ι ⊕ Cipher c) (n : ℕ ≃ β ⊕ CipherK c)

def enact : Activities G c := {
    reg:=fun i => (q i).elim R.reg (fun i => ⟨i.1,{i.1},by simp⟩)
    E:= fun i => (q i).elim R.ink (fun _ _ => 0)
    forced i := (n i).elim D.forced (fun i => ⟨i.val.1,i.val.2.1,i.property.1,i.property.2,fun _ => True⟩)
    K i := (n i).elim D.ink (fun _ _ => 0)}

-- transport even reserve supports. -/


variable {P : BudgetPoint}








def add (P : BudgetPoint) (x : Config G c) := ∑' i,masked P.threshold (R.range i) (R.ink i) x

/-- Retrieve labels from indexed arrays at the true V. Used with summability. -/
lemma submits (V : Config G c) :
    (R.enact D q n).additive P V = R.add P V ∧ (R.enact D q n).gas P V = ∑' i,D.record P V i := by
  constructor
  · unfold Activities.additive Activities.regularOccurrence enact; rw [← q.symm.tsum_eq]
    simp only [q.apply_symm_apply]
    unfold add
    let v i:=masked P.threshold (R.range i) (R.ink i) V
    refine tsum_eq_tsum_of_ne_zero_bij (g:=v) (fun i => Sum.inl i.val)
      (Sum.inl_injective.comp Subtype.val_injective) ?_ (fun _ => rfl)
    rintro (i|i) hi
    · exact ⟨⟨i,hi⟩,rfl⟩
    exfalso; apply hi
    simp [masked, Set.indicator]
  -- support equivalence
  let A:=R.enact D q n
  let f b := A.gasOccurrence P b V; let g:= D.record P V
  let k (i : β) := n.symm (Sum.inl i)
  have hi : Injective k:=n.symm.injective.comp Sum.inl_injective
  let e := fun s : Finset β => s.image k
  have hs : Injective e := Finset.image_injective hi
  have hh i : A.forced (k i)=D.forced i := by unfold A k enact; simp
  have hK i : A.K (k i)=D.ink i := by unfold A k enact; simp
  have he (s) : f (e s)=g s := by
    have hq : A.admissible P V (e s) ↔ D.covered P V s := by
      unfold Activities.admissible Brand.covered e
      rw [image_biUnion]; simp only [hh]
      apply and_congr_left; intro _
      constructor
      · intro h a ha b hb H
        have ht := h (Finset.mem_image_of_mem k ha) (Finset.mem_image_of_mem k hb) (hi.ne H)
        simp_rw [hh] at ht; exact ht
      intro h i hh' j hj hn
      obtain ⟨i,hi,rfl⟩:=mem_image.mp hh'; obtain ⟨j,hj',rfl⟩:=mem_image.mp hj
      rw [hh,hh]; exact h hi hj' (mt (congr_arg k) hn)
    unfold f g Brand.record Activities.gasOccurrence
    split
    · rename_i ht; rw [if_pos (hq.mp ht), show e s = s.image k by rfl,prod_image hi.injOn]; simp_rw [hK]
    rename_i ht; rw [if_neg (mt hq.mpr ht)]
  change (∑' i,f i)=∑' j,g j
  refine tsum_eq_tsum_of_ne_zero_bij (fun i : support g => e i.val) (hs.comp Subtype.val_injective) ?_ (fun i => he _)
  intro b hb
  have hp (i) (hi : i∈b) : ∃ j,k j=i := by
    obtain ⟨j,hj⟩:=n.symm.surjective i
    subst i
    rcases j with j|j; exact ⟨_,rfl⟩
    change f _ ≠0 at hb; unfold f Activities.gasOccurrence at hb; split at hb
    · have he:= prod_ne_zero_iff.mp hb _ hi; simp [A,enact] at he
    exact (hb rfl).elim
  choose v hv using hp
  let s := b.attach.image fun i => v i.val i.property
  have ht : e s=b := by
    ext i; constructor
    · intro h
      obtain ⟨j,h1,rfl⟩:=mem_image.mp h
      obtain ⟨j1,h1,rfl⟩:=mem_image.mp h1
      rw [hv]; exact j1.property
    intro he
    exact Finset.mem_image.mpr ⟨_,mem_image_of_mem _ (Finset.mem_attach b ⟨_,he⟩),hv i he⟩
  refine ⟨⟨s,?_⟩,ht⟩; rw [mem_support,← he,ht]; exact hb

end Room
end YM.SectorNext.Reconnect
