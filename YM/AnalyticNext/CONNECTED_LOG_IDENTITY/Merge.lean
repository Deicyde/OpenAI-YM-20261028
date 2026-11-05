import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Covered
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Exponential
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Repeats
import YM.Euclid.Table

set_option warningAsError false

/-!
# A forced set with exponential attaching letters

Only letters incident to the OLD forced family are allowed; check this
in both directions of the merger. Keep earlier K-vs-K exclusions (on
THEIR geometry) through the new complete-footprint merge. The lemma
is parametric in attaching letters and signs. It doesn't drop or move
any masks in their weights.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.Attach
open Lattice Wilson RG AbsoluteSums AbsoluteSums.Multiple Finset Filter Function
open scoped Classical BigOperators Topology
variable {ι κ : Type*} {n : Side}

/-- Can allow halo enlargement when merging. Represent older conflict test by `Y` and incidence
of an attaching letter by `X0` vs `Y` and reconnection geometry by possibly larger `X` vs `Y1`.
This never forbids two in an OLD selection on the enlarged test; they now have to merge.
-/
def reaches (Y : κ → Support n) (X0 : ι → Support n) (A : Finset κ) (i : ι) :=
  ¬ Disjoint (A.biUnion Y) (X0 i)

lemma reaches_iff (Y : κ → Support n) (X0 : ι → Support n) (A : Finset κ) (i : ι) :
    reaches Y X0 A i ↔ ∃ j∈A, ¬ Disjoint (Y j) (X0 i) := by
  unfold reaches; rw [disjoint_biUnion_left]; push Not; rfl

def Internal (Y : κ → Support n) (X0 : ι → Support n) (s : Finset (κ ⊕ ι)) :=
  Apart Y s.toLeft ∧ ∀ i∈s.toRight,reaches Y X0 s.toLeft i

def legal (Y : κ → Support n) (X0 : ι → Support n) (r : Reps (κ ⊕ ι)) :=
  Singles r ∧ Internal Y X0 r.1

private lemma meet_loose {x y A B : Support n} (hx : x⊆A) (hy : y⊆B) (h : ¬ Disjoint x y) : ¬ Disjoint A B := by
  obtain ⟨i,hi,hj⟩ := not_disjoint_iff.mp h; exact not_disjoint_iff.mpr ⟨_,hx hi,hy hj⟩

private lemma mem_l {s : Finset (κ ⊕ ι)} {i : κ} : i∈s.toLeft ↔ Sum.inl i∈s := by
  conv_rhs => rw [← s.toLeft_disjSum_toRight,inl_mem_disjSum]

private lemma mem_r {s : Finset (κ ⊕ ι)} {i : ι} : i∈s.toRight ↔ Sum.inr i∈s := by
  conv_rhs => rw [← s.toLeft_disjSum_toRight,inr_mem_disjSum]

private def test (Y : κ → Support n) (X0 : ι → Support n) : κ ⊕ ι → Finset (κ ⊕ ι) → Prop
  | .inl i => fun s => ∀ j∈s.toLeft,i≠j → Disjoint (Y i) (Y j)
  | .inr i => fun s => reaches Y X0 s.toLeft i

private lemma checked (Y Y1 : κ → Support n) (X0 X : ι → Support n)
    (hl : ∀ i,Y i ⊆ Y1 i) (hr : ∀ i,X0 i⊆X i) (s : Finset (κ ⊕ ι)) :
    Internal Y X0 s ↔ internal (both Y1 X) (test Y X0) s := by
  constructor
  · rintro ⟨h1,h2⟩ (i|i) hi
    · intro j hj hn; exact h1 (mem_l.mpr hi) (mem_l.mpr ((view_mem ..).mp (mem_l.mp hj)).1) hn
    change reaches Y X0 _ i
    rw [reaches_iff]
    obtain ⟨j,hj,he⟩ := (reaches_iff ..).mp (h2 i (mem_r.mpr hi))
    refine ⟨j,mem_l.mpr ((view_mem ..).mpr ⟨mem_l.mp hj,?_⟩),he⟩
    exact fun e => meet_loose (hl j) (hr i) he e.symm
  intro h
  constructor
  · intro i hi j hj hn
    by_contra he
    have ht := h _ (mem_l.mp (show i∈s.toLeft from hi))
    exact he (ht j (mem_l.mpr ((view_mem ..).mpr ⟨mem_l.mp hj,meet_loose (hl i) (hl j) he⟩)) hn)
  intro i hi
  obtain ⟨j,hj,he⟩ := (reaches_iff ..).mp (h _ (mem_r.mp hi))
  exact (reaches_iff ..).mpr ⟨j,mem_l.mpr ((view_mem ..).mp (mem_l.mp hj)).1,he⟩

lemma singles_iff (Y : κ → Support n) (X : ι → Support n) (r : Reps (κ ⊕ ι)) :
    let T := both Y X
    Singles r ↔ ∀ p∈detonate T r,Singles p.val := by
  intro T
  let H : κ ⊕ ι → ℕ → Prop := Sum.elim (fun _ a => a=0) fun _ _ => True
  have he (r : Reps (κ ⊕ ι)) : Singles r ↔ ∀ i∈r.1,H i (repeatRead r i) := by
    constructor
    · intro h i hi; cases i
      · exact h _ (mem_l.mpr hi)
      trivial
    intro h i hi; exact h (.inl i) (mem_l.mp hi)
  simp_rw [he]; exact repeat_all T r H

lemma legal_factors (Y Y1 : κ → Support n) (X0 X : ι → Support n)
    (hl : ∀ i,Y i ⊆ Y1 i) (hr : ∀ i,X0 i⊆X i) (r : Reps (κ ⊕ ι)) :
    let T := both Y1 X
    legal Y X0 r ↔ ∀ p∈detonate T r, legal Y X0 p.val := by
  intro T
  have h := singles_iff Y1 X r
  change Singles r ↔ ∀ p∈detonate T r,_ at h
  have he (r : Reps (κ ⊕ ι)) := checked Y Y1 X0 X hl hr r.1
  simp_rw [legal, he]
  change Singles r ∧ internal T (test Y X0) r.fst ↔ _
  rw [h,repeat_internal]
  constructor
  · exact fun hh i hi => ⟨hh.1 i hi,hh.2 i hi⟩
  intro hh; exact ⟨fun i hi => (hh i hi).1,fun i hi => (hh i hi).2⟩

/-- At least one d in a charged nonempty component, independent of flags V. -/
lemma old_inside (Y : κ → Support n) (X0 : ι → Support n) (r : Reps (κ ⊕ ι)) (h : legal Y X0 r)
    (he : r.1.Nonempty) : r.1.toLeft.Nonempty := by
  obtain ⟨i,hi⟩ := he
  rcases i with i|i
  · exact ⟨_,mem_l.mpr hi⟩
  obtain ⟨j,hj,-⟩ := (reaches_iff ..).mp (h.2.2 _ (mem_r.mpr hi))
  exact ⟨j,hj⟩

section Sum
variable (Y Y1 I : κ → Support n) (X0 X : ι → Support n) (D : Support n) (d : κ → ℝ) (a : ι → ℝ)

def entry (A : Finset κ) (i : ι) := if reaches Y X0 A i then a i else 0

def paid (A : Finset κ) := gasTerm Y I D d A * Real.exp (∑' i,entry Y X0 a A i)

/-- One actual family in the exponential expansion. -/
def bill (r : Reps (κ ⊕ ι)) :=
  if legal Y X0 r then manyW (Sum.elim d a) r else 0

def charged (r : Reps (κ ⊕ ι)) := if r.fst.biUnion (onlyL I) = D then bill Y X0 d a r else 0

lemma join_charged (A : Finset κ) (p : Reps ι) :
    gasTerm Y I D d A * manyW (entry Y X0 a A) p = charged Y I X0 D d a (join (A,p)) := by
  have hi : (join (A,p)).fst.toLeft = A := toLeft_disjSum
  have hh : (join (A,p)).fst.toRight = p.1 := toRight_disjSum
  unfold charged
  rw [show (join (A,p)).fst.biUnion (onlyL I) = A.biUnion I from ?_]
  swap
  · change (A.disjSum p.1).biUnion _ = _; rw [disj_union]; simp
  unfold bill legal Internal gasTerm Records
  rw [hi,hh]
  by_cases hc : A.biUnion I = D <;> by_cases hs : Apart Y A
  · simp only [hc,hs, join_singles,true_and,if_true]; split
    next ht =>
      rw [join_pay,print_counts,print_counts]; congr 1; refine prod_congr rfl fun i h => ?_
      unfold counted entry; rw [if_pos (ht _ h)]
    next ht =>
      push Not at ht; obtain ⟨i,hm,ht⟩ := ht
      rw [print_counts,prod_eq_zero hm (show counted p (entry Y X0 a A) i=0 from ?_),mul_zero]
      unfold counted entry; rw [if_neg ht,pow_succ,mul_zero,zero_div]
  · simp [hs]
  · simp [hc]
  simp [hc]

lemma entry_norm (A : Finset κ) (i : ι) : ‖entry Y X0 a A i‖ ≤ ‖a i‖ := by
  unfold entry; split
  · exact le_rfl
  rw [norm_zero]; exact norm_nonneg _

lemma charged_absolute (hd : Summable fun i => ‖d i‖) (ha : Summable fun i => ‖a i‖) :
    Summable (fun r => ‖charged Y I X0 D d a r‖) := by
  apply ((exponential _ (joint_absolute a d ha hd)).1).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i; unfold charged bill; split
  · split
    · exact le_rfl
    rw [norm_zero]; exact norm_nonneg _
  rw [norm_zero]; exact norm_nonneg _

lemma charged_sum (hd : Summable fun i => ‖d i‖) (ha : Summable fun i => ‖a i‖) :
    (∑' A,paid Y I X0 D d a A) = ∑' r, charged Y I X0 D d a r := by
  let f := charged Y I X0 D d a
  have he : Function.support f ⊆ Set.range join := by
    intro i hi
    have hh : f i ≠ 0 := hi
    unfold f charged bill at hh; split at hh
    · split at hh
      next ht => exact ⟨_,join_retract i ht.1⟩
      next ht => contradiction
    contradiction
  have hs := charged_absolute Y I X0 D d a hd ha
  have hh := hs.of_norm.comp_injective join_inj
  change Summable (fun i => f (join i)) at hh
  rw [← join_inj.tsum_eq he,hh.tsum_prod]
  apply tsum_congr; intro A
  have hw := ha.of_nonneg_of_le (fun i => norm_nonneg (entry Y X0 a A i)) (entry_norm Y X0 a A)
  unfold paid; rw [(exponential _ hw).2,← tsum_mul_left]; exact tsum_congr (join_charged Y I X0 D d a A)

-- Complete support at merger is X,Y1. The following formula on
-- RepeatSpecies still allows addresses failing internal eligibility (as
-- zeros). We'll reindex it into K cells.
lemma bill_parts (hl : ∀ i,Y i⊆ Y1 i) (hr : ∀ i,X0 i⊆ X i) (r : Reps (κ ⊕ ι)) :
    bill Y X0 d a r = ∏ p∈detonate (both Y1 X) r,bill Y X0 d a p.val := by
  let T := both Y1 X
  have hh := legal_factors Y Y1 X0 X hl hr r
  change legal Y X0 r ↔ ∀ p∈detonate T r,_ at hh
  unfold bill; split
  next he => rw [many_parts T]; exact prod_congr rfl fun p hp => (if_pos ((hh.mp he) _ hp)).symm
  next he =>
    have he := mt hh.mpr he
    push Not at he; obtain ⟨p,hp,ht⟩ := he
    exact (prod_eq_zero hp (if_neg ht)).symm

/-- Keep even addresses failing internal checks; may reprice/reuse the
address alphabet across several expansions. -/
abbrev Species' := {p : RepeatSpecies (both Y1 X) // p.val.1.toLeft.Nonempty}

def zone (p : Species' Y1 X) := rGround (both Y1 X) p.val
def hold (p : Species' Y1 X) := rOwned (both Y1 X) (onlyL I) p.val

lemma print_hold (p : Species' Y1 X) : hold Y1 I X p = p.val.val.fst.toLeft.biUnion I := by
  change p.val.val.fst.biUnion (onlyL I)=_
  conv_lhs => rw [← p.val.val.fst.toLeft_disjSum_toRight,disj_union]
  simp

lemma hold_nonempty (p : Species' Y1 X) (hi : ∀ i,(I i).Nonempty) : (hold Y1 I X p).Nonempty := by
  rw [print_hold]; obtain ⟨i,he⟩ := p.property; obtain ⟨x,hx⟩ := hi i
  exact ⟨x,mem_biUnion.mpr ⟨_,he,hx⟩⟩

lemma hold_zone (p : Species' Y1 X) (hi : ∀ i,I i ⊆ Y1 i) : hold Y1 I X p ⊆ zone Y1 X p :=
  owned_ground (both Y1 X) (onlyL I) (fun i => by rcases i with i|i; exact hi i; exact empty_subset _) _

/-- Actual output eligibility, apart from possible further explicit
extra tests retained in d, a or the spelling. -/
def merged (p : Species' Y1 X) :=
  if zone Y1 X p ∩ D = hold Y1 I X p then bill Y X0 d a p.val.val else 0

lemma reindex_forced {ν τ : Type*} (e : ν ↪ τ) (X I : τ → Support n) (D : Support n) (w : τ → ℝ)
    (s : Finset ν) :
    gasTerm X I D w (s.map e) = gasTerm (fun i => X (e i)) (fun i => I (e i)) D (fun i => w (e i)) s := by
  have he : Apart X (s.map e) ↔ Apart (fun i => X (e i)) s := by
    constructor
    · intro h i hi j hj hh; exact h (mem_map.mpr ⟨_,hi,rfl⟩) (mem_map.mpr ⟨_,hj,rfl⟩) (e.injective.ne hh)
    intro h i hi j hj hh
    obtain ⟨i,hi',rfl⟩ := mem_map.mp (show i∈s.map e from hi)
    obtain ⟨j,hj',rfl⟩ := mem_map.mp (show j∈s.map e from hj)
    exact h hi' hj' (fun h => hh (congr_arg _ h))
  have hh : (s.map e).biUnion I = s.biUnion (fun i => I (e i)) := by
    ext i; simp
  simp only [gasTerm,Records,he,hh,Finset.prod_map]

lemma forced_outside {ν τ : Type*} (e : ν ↪ τ) (X I : τ → Support n) (D : Support n) (w : τ → ℝ)
    (h : ∀ i,w i≠0 → i∈Set.range e) {s} (he : s ∉ Set.range (fun s : Finset ν => s.map e)) :
    gasTerm X I D w s = 0 := by
  have hr : ∃ i∈s, i∉Set.range e := by
    by_contra! H
    let l (i : ↥s) := (H i i.property).choose
    refine he ⟨s.attach.image l,?_⟩
    ext i; rw [Finset.mem_map]; constructor
    · rintro ⟨j,hj,rfl⟩; obtain ⟨i,_,rfl⟩ := mem_image.mp hj
      rw [(show e (l i)=i from (H _ i.property).choose_spec)]; exact i.property
    intro hi
    exact ⟨l ⟨i,hi⟩,mem_image_of_mem _ (mem_attach s _), (H _ hi).choose_spec⟩
  obtain ⟨i,hi,hI⟩ := hr
  unfold gasTerm; split
  · exact prod_eq_zero hi (by_contra fun hh => hI (h _ hh))
  rfl

/-- Reindex both the sum and absolute hypothesis; needed also
with decoder padding & translations later. -/
theorem project_forced {ν τ : Type*} (e : ν ↪ τ) (X I : τ → Support n) (D : Support n) (w : τ → ℝ)
    (h : ∀ i,w i≠0 → i∈Set.range e) :
    let f := gasTerm X I D w
    let g := gasTerm (fun i => X (e i)) (fun i => I (e i)) D (fun i => w (e i))
    (Summable (fun i => ‖f i‖) ↔ Summable (fun i => ‖g i‖)) ∧ (∑' s,f s) = ∑' s,g s := by
  intro f g
  let k := fun i : Finset ν => i.map e
  have he := Finset.map_injective e
  change Injective k at he
  have hh s (h' : s ∉ Set.range k) : f s=0 := forced_outside e X I D w h h'
  have hl : g = f ∘ k := funext fun i => (reindex_forced e X I D w i).symm
  rw [hl]; constructor
  · exact (he.summable_iff (f:=fun i => ‖f i‖) (fun i hi => by rw [hh i hi,norm_zero])).symm
  exact (he.tsum_eq (f:=f) (fun i hi => by by_contra h; exact hi (hh i h))).symm

/-- Exact reconnection with restored incidence and coverage; works also
on empty/zero-cost families. Witnesses forced by flags neither delete nor
introduce exclusions on paper; they require this identity (or similar). -/
theorem merge (hl : ∀ i,Y i⊆ Y1 i) (hr : ∀ i,X0 i⊆ X i) (hI : ∀ i, I i ⊆ Y i)
    (hX : ∀ i,(X i).Nonempty) (hY : ∀ i,(Y1 i).Nonempty)
    (hd : Summable fun i => ‖d i‖) (ha : Summable fun i => ‖a i‖) :
    let f := gasTerm (zone Y1 X) (hold Y1 I X) D (merged Y Y1 I X0 X D d a)
    Summable (fun s => ‖f s‖) ∧ (∑' A : Finset κ,paid Y I X0 D d a A) = ∑' s,f s := by
  intro f
  let T := both Y1 X
  let G := onlyL I (ι:=ι)
  let Z := rGround T
  let J := rOwned T G
  let v := fun i : RepeatSpecies T => bill Y X0 d a i.val
  have hn : ∀ i,(T i).Nonempty := by rintro (i | i) <;> first | exact hX i | exact hY i
  have hx := repeat_absolute T G D (bill Y X0 d a) v hn (fun i _ => bill_parts Y Y1 X0 X d a hl hr i)
  have hh := repeat_sum T G D (bill Y X0 d a) v hn (fun i _ => bill_parts Y Y1 X0 X d a hl hr i)
  let w := fun i : RepeatSpecies T => if Z i ∩ D = J i then v i else 0
  have hi : gasTerm Z J D v = gasTerm Z J D w :=
    funext (fun i => gasTerm_stamp Z J D v i (fun j => owned_ground T G (fun x => by
      rcases x with x|x; exact (hI x).trans (hl x); exact empty_subset _) (repeatSpeciesPlain T j)))
  let e : Species' Y1 X ↪ RepeatSpecies T := ⟨Subtype.val,Subtype.val_injective⟩
  have hp i (h : w i ≠ 0) : i ∈ Set.range e := by
    unfold w v bill at h; split at h
    · split at h
      next he => exact ⟨⟨i, old_inside _ _ _ he i.property.1⟩,rfl⟩
      next h => contradiction
    contradiction
  have he := charged_absolute Y I X0 D d a hd ha
  have hz := project_forced e Z J D w hp
  change Summable (fun s => ‖charged Y I X0 D d a s‖) ↔ Summable (fun i => ‖gasTerm Z J D v i‖) at hx
  change (∑' i,charged Y I X0 D d a i) = ∑' s,gasTerm Z J D v s at hh
  rw [hi] at hx hh
  exact ⟨hz.1.mp (hx.mp he), (charged_sum Y I X0 D d a hd ha).trans (hh.trans hz.2)⟩

end Sum
end YM.Push.LogIdentity.Attach
