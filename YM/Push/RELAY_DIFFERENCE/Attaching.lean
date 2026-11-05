import YM.Next.EXTRACTION.Tails
import YM.Work.B04

/-!
# Attach the bad-stencil discrepancy at birth into the ACTUAL covered gas

One-body initialization tool for : no extra exponent coefficient
on bad configurations from silently using regular entries there. Gather an
overlap into a *statically reserved* label (same H). Needs address room,
which we will specify exactly. This file does the density identity; the
estimates are in another.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference.Attach
open Function Set Filter MeasureTheory Lattice RG Wilson Source
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : Side} {X : Support n} {R : Rep G n}
local notation "Family'" => Finset ℕ

def home (R : Rep G n) (i : ℕ) := (R.activities.forced i).support
def boxes (R : Rep G n) (b : Family') : Support n := b.biUnion fun i => (R.activities.forced i).inventory

def isolated (R : Rep G n) (b : Family') := (b : Set ℕ).Pairwise fun i j => Disjoint (home R i) (home R j)

def collides (X : Support n) (R : Rep G n) (i : ℕ) := ¬ Disjoint (home R i) X

def paint (X : Support n) (R : Rep G n) (b : Family') : Family' := by
  classical exact b.filter (collides X R)
@[simp] lemma paint_eq (i : ℕ) (b : Family') : i ∈ paint X R b ↔ i∈b ∧ collides X R i := by simp [paint]

/-- the overlapping OLD labels. Nonempty by precise coverage at any bad
read. Indices, not occupancy patterns. -/
abbrev Catch (X : Support n) (R : Rep G n) :=
    {b : Family' // b.Nonempty ∧ (∀ i∈b, collides X R i) ∧ isolated R b}

namespace Catch
def cloth (p : Catch X R) := X ∪ p.val.biUnion (home R)
lemma insertLabel (p : Catch X R) {i} (h : i∈p.val) : home R i ⊆ p.cloth :=
  fun _ he => Finset.mem_union_right X (Finset.mem_biUnion.mpr ⟨i,h,he⟩)
end Catch

/-- Need enough actual forced addresses for the construction. E.g., arrange
spare alphabets at those levels with K=0 there. Need extraTest true for the
whole support flags test. Don't infer these from Moves or Bounds. -/
structure Slots (X : Support n) (R : Rep G n) where
  code : Catch X R ↪ ℕ
  exactCover p : home R (code p) = p.cloth
  inventories p : (R.activities.forced (code p)).inventory = boxes R p.val
  allowed p : ∀ U,(R.activities.forced (code p)).extraTest U

namespace Slots
variable (s : Slots X R)

open scoped Classical in
def assigned (D : Config G n → ℂ) (p : Catch X R) (U : Config G n) := if
    (R.activities.forced (s.code p)).eligible R.p.threshold U then
      D U * (∏ i∈p.val, (R.activities.K i U:ℂ)) else 0

open scoped Classical in
def out (D : Config G n → ℂ) (i : ℕ) : Config G n → ℂ := if h : i∈Set.range s.code then
    s.assigned D (Classical.choose h) else 0

lemma restored (D : Config G n → ℂ) (p : Catch X R) : s.out D (s.code p)=s.assigned D p := by
  classical
  unfold out; split
  · rename_i h; rw [s.code.injective (Classical.choose_spec h)]
  next h => exact False.elim (h ⟨p,rfl⟩)
end Slots

section Exact
variable {U : Config G n}

def Old (X : Support n) (R : Rep G n) (U : Config G n) : Set Family' :=
    {b | (R.activities.admissible R.p U b) ∧ (paint X R b).Nonempty}

def New (s : Slots X R) (U : Config G n) : Set Family' :=
    {b | (R.activities.admissible R.p U b) ∧ ∃ p, s.code p∈b}

abbrev Pieces (X : Support n) (R : Rep G n) (U : Config G n) :=
    {v : Catch X R × Family' // isolated R v.2 ∧ (∀ i∈v.2,Disjoint (home R i) v.1.cloth) ∧
         boxes R v.1.val ∪ boxes R v.2=flags R.p.threshold U}

variable (s : Slots X R)

namespace Pieces
variable (p : Pieces X R U)

lemma stays (hx : X.Nonempty) (q : Catch X R) : s.code q ∉ p.val.2 := by
  intro h
  obtain ⟨i,hi⟩ := hx
  have hu := p.property.2.1 (s.code q) h
  rw [s.exactCover q] at hu
  exact Finset.disjoint_left.mp hu (Finset.mem_union_left _ hi) (Finset.mem_union_left _ hi)

lemma split : Disjoint p.val.2 p.val.1.val := by
  apply Finset.disjoint_left.mpr
  intro a h v
  obtain ⟨i,hi⟩ := (R.activities.forced a).inventory_ne.mono (R.activities.forced a).inventory_sup
  exact Finset.disjoint_left.mp (p.property.2.1 a h) hi (Catch.insertLabel _ v hi)

lemma painted : paint X R (p.val.1.val ∪ p.val.2) = p.val.1.val := by
  ext i
  rw [paint_eq]; constructor
  · rintro ⟨hi,hg⟩; rcases Finset.mem_union.mp hi with H|H
    · exact H
    exact (hg (Finset.disjoint_of_subset_right (Finset.subset_union_left) (p.property.2.1 _ H))).elim
  intro h; exact ⟨Finset.mem_union_left _ h, p.val.1.property.2.1 _ h⟩

/-- Original and new sets BOTH test full global coverage. -/
def before (p : Pieces X R U) : Old X R U := ⟨p.val.1.val∪p.val.2, by
  refine ⟨⟨?_,?_⟩, by rw [p.painted]; exact p.val.1.property.1⟩
  · intro i hi j hj he
    rcases Finset.mem_union.mp hi with H|H <;> rcases Finset.mem_union.mp hj with h|h
    · exact p.val.1.property.2.2 H h he
    · exact (Finset.disjoint_of_subset_right (p.val.1.insertLabel H) (p.property.2.1 j h)).symm
    · exact Finset.disjoint_of_subset_right (p.val.1.insertLabel h) (p.property.2.1 i H)
    exact p.property.1 H h he
  rw [Finset.union_biUnion]; exact p.property.2.2⟩

def after (s : Slots X R) (p : Pieces X R U) : New s U := ⟨insert (s.code p.val.1) p.val.2, by
  refine ⟨⟨?_,?_⟩,⟨p.val.1,Finset.mem_insert_self ..⟩⟩
  · have ha (i : ℕ) (h : i∈p.val.2) : Disjoint (home R i) (home R (s.code p.val.1)) := (s.exactCover _).symm ▸ p.property.2.1 _ h
    intro i hi j hj he; rcases Finset.mem_insert.mp hi with H|H <;> rcases Finset.mem_insert.mp hj with h|h
    · exact False.elim (he (H.trans h.symm))
    · subst i; exact (ha _ h).symm
    · subst j; exact ha _ H
    exact p.property.1 H h he
  rw [Finset.biUnion_insert,s.inventories]; exact p.property.2.2⟩

lemma recognized : Bijective (before (X:=X) (U:=U) (R:=R)) := by
  constructor
  · intro p q h
    have he : p.val.1.val ∪ p.val.2 = q.val.1.val ∪ q.val.2 := congr_arg Subtype.val h
    have ht : p.val.1.val = q.val.1.val := by rw [←p.painted, he, q.painted]
    apply Subtype.ext; refine Prod.ext ?_ ?_
    · exact Subtype.ext ht
    · change p.val.2=q.val.2
      have hh (p : Pieces X R U) : (p.val.1.val ∪ p.val.2) \ p.val.1.val = p.val.2 := by
        ext i; simp only [Finset.mem_sdiff,Finset.mem_union]
        have he : i∈p.val.2 → i∉p.val.1.val := fun hi => Finset.disjoint_left.mp p.split hi
        tauto
      rw [← hh p, he, ht, hh q]
  intro b
  let x := paint X R b.val
  have hB := b.property
  have hy : x ⊆ b.val := fun i hi => (paint_eq i b.val).mp hi |>.1
  let p : Catch X R := ⟨x, hB.2,fun i hi => ((paint_eq i b.val).mp hi).2, fun a h i hi he => hB.1.1 (hy h) (hy hi) he⟩
  let z := b.val \ x
  have hz : p.val ∪ z=b.val := by ext i; have H := fun (h : i∈x) => hy h; simp only [p,z,Finset.mem_union,Finset.mem_sdiff];tauto
  suffices H : ∃ Q : Pieces X R U,Q.val = (p,z) by
    obtain ⟨Q,hQ⟩ := H; refine ⟨Q,Subtype.ext ?_⟩; change Q.val.1.val∪Q.val.2=b.val; rw [hQ]; exact hz
  refine ⟨⟨(p,z),?_,?_,?_⟩,rfl⟩
  · intro i hi j hj he; exact hB.1.1 (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 he
  · intro i hi
    obtain ⟨hv,hw⟩ := Finset.mem_sdiff.mp hi
    have hd : Disjoint (home R i) X := by
      by_contra hh; exact hw ((paint_eq i b.val).mpr ⟨hv,hh⟩)
    apply Finset.disjoint_left.mpr
    intro j hj hk
    rcases Finset.mem_union.mp hk with he|he; exact Finset.disjoint_left.mp hd hj he
    obtain ⟨l,hl,hH⟩ := Finset.mem_biUnion.mp he
    exact Finset.disjoint_left.mp (hB.1.1 hv (hy hl) (fun ho => hw (ho ▸ hl))) hj hH
  · change boxes R p.val ∪ boxes R z=_
    rw [boxes,boxes,←Finset.union_biUnion,hz]; exact hB.1.2

lemma recovered (hx : X.Nonempty) : Bijective (after (U:=U) s) := by
  constructor
  · intro p q h
    have he : insert (s.code p.val.1) p.val.2=insert (s.code q.val.1) q.val.2 := congr_arg Subtype.val h
    have ht : s.code p.val.1∈insert (s.code q.val.1) q.val.2 := by rw [← he]; exact Finset.mem_insert_self ..
    have hp : p.val.1=q.val.1 := s.code.injective ((Finset.mem_insert.mp ht).resolve_right (q.stays s hx _))
    apply Subtype.ext; apply Prod.ext hp
    rw [hp] at he
    have he' := congr_arg (fun S : Family' => S.erase (s.code q.val.1)) he
    have h₁ := p.stays s hx q.val.1
    have h₂ := q.stays s hx q.val.1
    simpa only [Finset.erase_insert h₁, Finset.erase_insert h₂] using he'
  intro b
  obtain ⟨p,hp⟩ := b.property.2
  let z := b.val.erase (s.code p)
  have he : insert (s.code p) z=b.val := Finset.insert_erase hp
  suffices H : ∃ Q : Pieces X R U,Q.val=(p,z) by
    obtain ⟨Q,hQ⟩ := H; refine ⟨Q,Subtype.ext ?_⟩; change insert _ _ = _; simp only [hQ]; exact he
  refine ⟨⟨(p,z),?_,?_,?_⟩,rfl⟩
  · intro i hi j hj ho; exact b.property.1.1 (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hj).2 ho
  · intro i hi
    obtain ⟨hf,hq⟩ := Finset.mem_erase.mp hi
    rw [←s.exactCover]; exact b.property.1.1 hq hp hf
  have hw : boxes R b.val=_ := b.property.1.2
  rw [←he,boxes,Finset.biUnion_insert,s.inventories] at hw; exact hw

/-- The extra mask on a used address is exactly evaluated (even outside
its supporting term, needed for the identity). -/
lemma uses : (R.activities.forced (s.code p.val.1)).eligible R.p.threshold U := by
  refine ⟨?_,s.allowed p.val.1 U⟩
  have he : (flags R.p.threshold U)=boxes R (p.after s).val := (p.after s).property.1.2.symm
  conv_lhs => rhs; rw [he]
  ext i
  simp only [Finset.mem_inter, boxes,Finset.mem_biUnion]
  constructor
  · rintro ⟨hi,j,hj,hj'⟩
    by_cases hh : j=s.code p.val.1
    · rwa [hh] at hj'
    have hd : Disjoint (home R j) (home R (s.code p.val.1)) := (p.after s).property.1.1 hj (show s.code p.val.1∈(p.after s).val from Finset.mem_insert_self ..) hh
    exact False.elim (Finset.disjoint_left.mp hd ((R.activities.forced j).inventory_sup hj') hi)
  intro hi; exact ⟨(R.activities.forced _).inventory_sup hi,_,Finset.mem_insert_self ..,hi⟩
end Pieces

variable {d : ℕ} {F : Labels.Frame G d}

private lemma occurrence {D : Coefficient F n} {Q : Config G n → ℂ} (hv : D.forced = s.out Q) (hx : X.Nonempty)
    (b : Pieces X R U) : D.marked R (b.after s).val U =
      (R.activities.gasOccurrence R.p b.before.val U : ℂ) * Q U := by
  classical
  rw [Coefficient.marked, if_pos (b.after s).property.1,RG.Activities.gasOccurrence,
    if_pos b.before.property.1]
  rw [Finset.sum_eq_single (s.code b.val.1), hv, Slots.restored, Slots.assigned,if_pos (b.uses s)]
  · unfold Pieces.before Pieces.after; dsimp only
    rw [Finset.prod_union (b.split.symm), Finset.erase_insert (b.stays s hx _), Complex.ofReal_mul,
      Complex.ofReal_prod, Complex.ofReal_prod]; ring
  · intro i hi hp
    have ht := (Finset.mem_insert.mp hi).resolve_left hp
    have hg : i∉Set.range s.code := fun ⟨p,hp⟩ => b.stays s hx _ (hp.symm ▸ ht)
    rw [hv,Slots.out,dif_neg hg,Pi.zero_apply,zero_mul]
  exact fun h => False.elim (h (Finset.mem_insert_self ..))

/-- Multiply by a local remainder with at least one flag. *All* compatible
K families; no scope switch to K-average conditioning at the base stencil. -/
theorem realizes {Q : Config G n → ℂ} {D : Coefficient F n} (h : D.forced = s.out Q) (hx : X.Nonempty)
    (ha : Healthy R.p.threshold X U → Q U=0) :
    (∑' i, D.marked R i U) = (R.activities.gas R.p U:ℂ)*Q U := by
  classical
  let Z : Family' → ℂ := fun i => D.marked R i U
  let Y : Family' → ℂ := fun i => (R.activities.gasOccurrence R.p i U:ℂ)*Q U
  have hs : Function.support Z ⊆ New s U := by
    intro b hb
    change D.marked R b U ≠ 0 at hb
    unfold Coefficient.marked at hb; split at hb
    · rename_i hf; refine ⟨hf,?_⟩; by_contra hh
      push Not at hh
      refine hb (Finset.sum_eq_zero fun i hi => ?_)
      have hu : i∉Set.range s.code := fun ⟨p,hP⟩ => hh p (hP.symm ▸ hi)
      rw [h,Slots.out,dif_neg hu,Pi.zero_apply,zero_mul]
    exact (hb rfl).elim
  have ht : Function.support Y ⊆ Old X R U := by
    intro b hb
    change (R.activities.gasOccurrence R.p b U : ℂ)*Q U ≠ 0 at hb
    unfold RG.Activities.gasOccurrence at hb
    split at hb
    · rename_i hf
      refine ⟨hf,?_⟩
      have he : ¬Healthy R.p.threshold X U := fun hu => hb (by rw [ha hu, mul_zero])
      obtain ⟨x,hX,hx⟩ := Finset.not_disjoint_iff.mp he
      rw [←hf.2] at hx
      obtain ⟨a,ha,hv⟩ := Finset.mem_biUnion.mp hx
      exact ⟨a,(paint_eq _ _).mpr ⟨ha,Finset.not_disjoint_iff.mpr
        ⟨x,(R.activities.forced a).inventory_sup hv,hX⟩⟩⟩
    exact False.elim (hb (by simp))
  let L := Equiv.ofBijective _ (Pieces.recognized (R:=R) (U:=U) (X:=X))
  let B := Equiv.ofBijective _ (Pieces.recovered (U:=U) s hx)
  change (∑' i, Z i) = _
  rw [RG.Activities.gas,Complex.ofReal_tsum,←tsum_mul_right]
  change (∑' i, Z i) = ∑' i, Y i
  rw [← tsum_subtype_eq_of_support_subset hs, ← tsum_subtype_eq_of_support_subset ht]
  rw [←B.tsum_eq,←L.tsum_eq]
  exact tsum_congr fun i => occurrence s h hx i
end Exact
end YM.Push.RelayDifference.Attach
