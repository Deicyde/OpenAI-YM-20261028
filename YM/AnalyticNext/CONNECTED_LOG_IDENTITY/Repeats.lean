import Mathlib.Analysis.Normed.Group.Tannery
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Words
import YM.Push.ABSOLUTE_SUMS.Omissions

set_option warningAsError false

/-!
# Assemblies with repeats, for 

* One set of forced addresses, plus a multiset of cluster addresses;
  represent jointly with multiplicity 1 on the former (Lemma join).
* Split by the new connected components; identical cluster copies
  CANNOT be in distinct components. The inverse factorials thus split
  exactly (Lemma many_parts). Don't divide again by a factorial on the
  set of components.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity

open Lattice Wilson RG AbsoluteSums AbsoluteSums.Multiple Finset Filter Function Ursell
open scoped Classical BigOperators Topology

variable {ι κ : Type*} {n : Side}

/-- Extra repetitions (multiplicity minus 1) with zero padding off list. -/
def repeatRead (r : Reps ι) (i : ι) := if h : i∈r.1 then r.2 ⟨i,h⟩ else 0

lemma repeat_at (r : Reps ι) {i : ι} (hi : i∈r.1) : repeatRead r i = r.2 ⟨i,hi⟩ := dif_pos hi

lemma repeat_ext {r s : Reps ι} (h : r.1 = s.1)
    (he : ∀ i∈r.1,repeatRead r i = repeatRead s i) : r=s := by
  obtain ⟨r,a⟩ := r; obtain ⟨s,b⟩ := s
  dsimp only at h; subst s
  congr; exact funext fun i => by simpa only [repeatRead,dif_pos i.property] using he i i.property

/-- Print repetitions as a finset product for easy partitioning.
Note the `+1`. -/
def counted (r : Reps ι) (w : ι → ℝ) (i : ι) := w i^(repeatRead r i+1)/(repeatRead r i+1).factorial

lemma print_counts (r : Reps ι) (w : ι → ℝ) : manyW w r = ∏ i∈r.1,counted r w i := by
  rw [prod_subtype r.1 (p:=(·∈r.1)) (fun _ => Iff.rfl)]
  apply prod_congr rfl; intro i _; unfold counted; rw [repeat_at r i.property]

/-- Forced SET on the left (so exactly one each), arbitrary
restoration multiset on the right. -/
def join (p : Finset κ × Reps ι) : Reps (κ ⊕ ι) :=
  ⟨p.1.disjSum p.2.1, fun i => i.val.elim (fun _ => 0) (repeatRead p.2)⟩

def Singles (r : Reps (κ ⊕ ι)) := ∀ i∈r.1.toLeft, repeatRead r (Sum.inl i) = 0

lemma join_singles (p : Finset κ × Reps ι) : Singles (join p) := fun i hi => by
  rw [repeat_at _ (by simpa [join] using hi)]; rfl

lemma join_right (p : Finset κ × Reps ι) (i : ι) : repeatRead (join p) (.inr i) = repeatRead p.2 i := by
  by_cases h : i∈p.2.1
  · rw [repeat_at _ (inr_mem_disjSum.mpr h)]; rfl
  rw [repeatRead,repeatRead,dif_neg h, dif_neg (by simpa only [join,inr_mem_disjSum] using h)]

def unjoin (r : Reps (κ ⊕ ι)) : Finset κ × Reps ι :=
  (r.1.toLeft,⟨r.1.toRight,fun i => repeatRead r (Sum.inr i.val)⟩)

lemma retract_join (p : Finset κ × Reps ι) : unjoin (join p)=p := by
  apply Prod.ext (toLeft_disjSum)
  apply repeat_ext toRight_disjSum; intro i hi
  rw [repeat_at _ hi]; change repeatRead (join p) (.inr i) = _; rw [join_right]

lemma join_retract (r : Reps (κ ⊕ ι)) (h : Singles r) : join (unjoin r)=r := by
  apply repeat_ext toLeft_disjSum_toRight
  intro i hi
  rcases i with i|j
  · have he : i∈r.fst.toLeft := by
      change Sum.inl i ∈ r.fst.toLeft.disjSum r.fst.toRight at hi
      simpa using hi
    rw [h i he,repeat_at _ hi]; rfl
  · have he : j∈r.fst.toRight := by
      change Sum.inr j ∈ r.fst.toLeft.disjSum r.fst.toRight at hi
      simpa using hi
    rw [join_right,repeat_at _ he]; rfl

lemma join_inj : Injective (@join ι κ) := Function.LeftInverse.injective retract_join

lemma join_pay (p : Finset κ × Reps ι) (d : κ → ℝ) (w : ι → ℝ) :
    manyW (Sum.elim d w) (join p) = (∏ i∈p.1,d i) * manyW w p.2 := by
  rw [print_counts,print_counts, show (join p).1 = p.1.disjSum p.2.1 from rfl,prod_disjSum]
  congr 1
  · refine prod_congr rfl fun i hi => ?_
    unfold counted; have he : repeatRead (join p) (.inl i)=0 := by rw [repeat_at _ (inl_mem_disjSum.mpr hi)]; rfl
    rw [he]; simp
  refine prod_congr rfl fun i hi => ?_; unfold counted; rw [join_right]; rfl

section Pieces
variable (X : ι → Support n)

abbrev RepeatSpecies := {r : Reps ι // Ac.Spark X r.1}

def repeatSpeciesPlain (p : RepeatSpecies X) : Species X := ⟨p.val.1,p.property⟩
def rGround (p : RepeatSpecies X) := ground X (repeatSpeciesPlain X p)
def rOwned (I : ι → Support n) (p : RepeatSpecies X) := owned X I (repeatSpeciesPlain X p)

private def restrictTo (r : Reps ι) (p : Species X) : RepeatSpecies X :=
  ⟨⟨p.val,fun i => repeatRead r i.val⟩,p.property⟩

private lemma restrict_inj (r : Reps ι) : Injective (restrictTo X r) := fun _ _ h =>
  congr_arg (repeatSpeciesPlain X) h

def detonate (r : Reps ι) : Finset (RepeatSpecies X) :=
  (explode X r.1).image (restrictTo X r)

def toSets (s : Finset (RepeatSpecies X)) : Finset (Species X) := s.image (repeatSpeciesPlain X)

lemma rApart (r : Reps ι) : Apart (rGround X) (detonate X r) := by
  intro i hi j hj hn
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hi; obtain ⟨b,hb,rfl⟩ := mem_image.mp hj
  exact apart_explode X r.1 ha hb (fun h => hn (congr_arg _ h))

lemma detonated_plain (r : Reps ι) : toSets X (detonate X r)=explode X r.1 := by
  ext p; simp [toSets,detonate,repeatSpeciesPlain, restrictTo,p.property]

lemma repeat_here {r : Reps ι} {p : RepeatSpecies X} (h : p∈detonate X r) {i : ι}
    (hi : i∈p.val.1) : repeatRead p.val i = repeatRead r i := by
  obtain ⟨p,hp,rfl⟩ := mem_image.mp h
  rw [repeat_at _ hi]; rfl



lemma sets_apart {t : Finset (RepeatSpecies X)} (h : Apart (rGround X) t) : Apart (ground X) (toSets X t) := by
  intro i hi j hj e
  obtain ⟨i,ht,rfl⟩ := mem_image.mp hi; obtain ⟨j,hu,rfl⟩ := mem_image.mp hj
  exact h ht hu (fun hh => e (congr_arg _ hh))

def consolidate (t : Finset (RepeatSpecies X)) : Reps ι :=
  ⟨collect X (toSets X t), fun i => ∑ p∈t, repeatRead p.val i.val⟩

lemma consolidated (hX : ∀ i,(X i).Nonempty) {t : Finset (RepeatSpecies X)} (h : Apart (rGround X) t)
    {p : RepeatSpecies X} (ht : p∈t) {i : ι} (hi : i∈p.val.1) :
    repeatRead (consolidate X t) i = repeatRead p.val i := by
  rw [repeat_at _ (collect_incl X (mem_image_of_mem _ ht) hi)]
  change ∑ p∈t, _ = _
  apply sum_eq_single_of_mem p ht; intro j hj he
  unfold repeatRead; apply dif_neg; intro hh
  obtain ⟨x,hx⟩ := hX i
  exact Finset.disjoint_left.mp (h hj ht he)
    (species_ground X (p:=repeatSpeciesPlain X j) hh hx) (species_ground X (p:=repeatSpeciesPlain X p) hi hx)

lemma consolidate_detonate (hX : ∀ i,(X i).Nonempty) (r : Reps ι) : consolidate X (detonate X r) = r := by
  have he : (consolidate X (detonate X r)).1 = r.1 := by
    change collect X _ = r.1; rw [detonated_plain,collect_explode]
  apply repeat_ext he; intro i hi
  obtain ⟨p,hp,hi'⟩ := mem_biUnion.mp hi
  obtain ⟨p,hP,rfl⟩ := mem_image.mp hp
  rw [consolidated X hX (rApart X r) hP hi', repeat_here X hP hi']

theorem detonate_consolidate (hX : ∀ i,(X i).Nonempty) (t : Finset (RepeatSpecies X)) (h : Apart (rGround X) t) :
    detonate X (consolidate X t)=t := by
  have he (p : RepeatSpecies X) (hp : p∈t) : restrictTo X (consolidate X t) (repeatSpeciesPlain X p) = p := by
    apply Subtype.ext; refine repeat_ext ?_ ?_; exact rfl
    intro i hi; rw [repeat_at _ hi]; exact consolidated X hX h hp hi
  unfold detonate
  change (explode X (collect X (toSets X t))).image (restrictTo X (consolidate X t))=t
  rw [explode_collect X _ (sets_apart X h),toSets, image_image]
  ext p; rw [mem_image]; constructor
  · rintro ⟨i,hi,hh⟩; rwa [← hh,Function.comp_apply,he _ hi]
  intro hp
  exact ⟨p,hp,he _ hp⟩

lemma detonate_inj (hX : ∀ i,(X i).Nonempty) : Injective (detonate X) :=
  Function.LeftInverse.injective (consolidate_detonate X hX)

/-- Inverse repetition factorials split exactly. -/
lemma many_parts (w : ι → ℝ) (r : Reps ι) :
    manyW w r = ∏ p∈detonate X r,manyW w p.val := by
  rw [detonate,prod_image (restrict_inj X r).injOn,print_counts,per_parts X r.1]
  apply prod_congr rfl; intro i hi
  rw [print_counts]; apply prod_congr rfl; intro j hj
  unfold counted; rw [repeat_here X (p:=restrictTo X r i) (mem_image_of_mem _ hi) hj]

lemma repeat_owned (I : ι → Support n) (r : Reps ι) : (detonate X r).biUnion (rOwned X I)=r.1.biUnion I := by
  have he : (detonate X r).biUnion (rOwned X I) = (toSets X (detonate X r)).biUnion (owned X I) := by
    ext x; rw [mem_biUnion,mem_biUnion]; constructor
    · rintro ⟨i,hi,h⟩; exact ⟨_,mem_image_of_mem _ hi,h⟩
    rintro ⟨i,hi,h⟩; obtain ⟨i,hI,rfl⟩ := mem_image.mp hi; exact ⟨i,hI,h⟩
  rw [he,detonated_plain,explode_owned]

lemma repeat_internal (test : ι → Finset ι → Prop) (r : Reps ι) :
    internal X test r.1 ↔ ∀ p ∈ detonate X r, internal X test p.val.1 := by
  rw [internal_iff X, detonate, Finset.forall_mem_image]; rfl



lemma repeat_all (r : Reps ι) (H : ι → ℕ → Prop) :
    (∀ i∈r.1,H i (repeatRead r i)) ↔
      ∀ p∈detonate X r,∀ i∈p.val.1,H i (repeatRead p.val i) := by
  have hh := detonated_plain X r
  constructor
  · intro h p hp i hi
    rw [repeat_here X hp hi]
    have hv : repeatSpeciesPlain X p ∈ explode X r.1 := by rw [← hh]; exact mem_image_of_mem _ hp
    exact h i ((Ac.lives X r.1 ((exploded X _).mp hv)).1 hi)
  intro h i hi
  have hv := hi
  rw [← collect_explode X r.fst, ← hh] at hv
  obtain ⟨p,hp,hi'⟩ := mem_biUnion.mp hv
  obtain ⟨p,hP,rfl⟩ := mem_image.mp hp
  rw [← repeat_here X hP (show i ∈ p.val.1 from hi')]; exact h _ hP i hi'

section Reindex
variable (I : ι → Support n) (D : Support n)

lemma repeat_gas (u : Reps ι → ℝ) (w : RepeatSpecies X → ℝ)
    (hf : ∀ r : Reps ι, r.1.biUnion I = D → u r = ∏ p∈detonate X r, w p) (r : Reps ι) :
    (if r.1.biUnion I = D then u r else 0) = gasTerm (rGround X) (rOwned X I) D w (detonate X r) := by
  simp only [gasTerm,Records,rApart,repeat_owned,true_and]; split
  next h => exact hf _ h
  next => rfl

lemma repeat_outside (w : RepeatSpecies X → ℝ) (hn : ∀ i,(X i).Nonempty)
    {s} (h : s ∉ Set.range (detonate X)) : gasTerm (rGround X) (rOwned X I) D w s = 0 :=
  if_neg (fun e => h ⟨_,detonate_consolidate X hn s e.1⟩)

theorem repeat_sum (u : Reps ι → ℝ) (w : RepeatSpecies X → ℝ)
    (hn : ∀ i,(X i).Nonempty)
    (hf : ∀ r : Reps ι, r.1.biUnion I = D → u r = ∏ p∈detonate X r, w p) :
    let f := gasTerm (rGround X) (rOwned X I) D w
    let g (r : Reps ι) := if r.1.biUnion I = D then u r else 0
    (∑' r,g r) = ∑' s,f s := by
  intro f g
  rw [← (detonate_inj X hn).tsum_eq (f:=f) (fun s hs => by by_contra h; exact hs (repeat_outside X I D w hn h))]
  exact tsum_congr (repeat_gas X I D u w hf)

theorem repeat_absolute (u : Reps ι → ℝ) (w : RepeatSpecies X → ℝ)
    (hn : ∀ i,(X i).Nonempty)
    (hf : ∀ r : Reps ι, r.1.biUnion I = D → u r = ∏ p∈detonate X r, w p) :
    let f := gasTerm (rGround X) (rOwned X I) D w
    let g (r : Reps ι) := if r.1.biUnion I = D then u r else 0
    Summable (fun r => ‖g r‖) ↔ Summable (fun r => ‖f r‖) := by
  intro f g
  have eq : (fun r => ‖g r‖) =
      ((fun r => ‖f r‖) ∘ detonate X) := funext fun r => congr_arg (fun x : ℝ => ‖x‖) (repeat_gas X I D u w hf r)
  exact eq.symm ▸ (detonate_inj X hn).summable_iff (f:=fun r => ‖f r‖) (fun r hr => by
    unfold f; rw [repeat_outside X I D w hn hr,norm_zero])


end Reindex
end Pieces
end YM.Push.LogIdentity
