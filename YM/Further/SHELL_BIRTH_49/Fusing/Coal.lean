import YM.Ac.Nodes
import YM.RG.Activities

/-!
# Distinct-address reconstruction along two simultaneous interactions

Overlap of the footprint only joins material terms. An otherwise dry
term that already connects by region tags to a material term is itself
material. Implement as one graph, with site coordinates hidden on the
nonmaterial region components. All occurrences selected outside the gas
(dry/residual etc.) are still counted in this graph where appropriate.
Letters in different cores may have overlapping supports, but not tags.
Keep arbitrary overlaps, don't assume region stencils are native disjoint;
works for ceil phases and contrasts, and unbounded halos.

Generalizes Ac/Nodes specialization (`X` : Support n) to a
sum-coded interaction that must be recomputed after tentative deletion,
and pays true lattice cover via Ac.Spark.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ShellBirth49.Fusing
open Function Finset Relation Lattice
open scoped Classical

namespace Collide
variable {I V : Type*} (q : I → Finset V) (s : Finset I)

def meets (i j : I) := ∃ x, x∈q i ∧ x∈q j
abbrev bond := fun i j => i ∈ s ∧ j∈s ∧ meets q i j
def link (i j : I) := ReflTransGen (bond q s) i j
def core (i : I) := s.filter (link q s i)
def spark := s.Nonempty ∧ ∀ i∈s,∀ j∈s,link q s i j
variable [DecidableEq I]
abbrev parts := s.image (core q s)

variable {s}
omit [DecidableEq I] in
lemma aglow {i j : I} : j∈core q s i ↔ j∈s ∧ link q s i j := mem_filter
omit [DecidableEq I] in
lemma swap {i j} (h : link q s i j) : link q s j i := by
  induction h with
  | refl => exact .refl
  | tail _ hk ih =>
    obtain ⟨h1,h2,x,h3,h4⟩ := hk
    exact .head ⟨h2,h1,x,h4,h3⟩ ih

omit [DecidableEq I] in
lemma same {i j} (h : link q s i j) : core q s i = core q s j := by
  ext k; rw [aglow q,aglow q]; exact and_congr_right fun _ =>
    ⟨fun hh => ReflTransGen.trans (swap q h) hh,fun hh => ReflTransGen.trans h hh⟩
omit [DecidableEq I] in
lemma warm {i j : I} (hj : j∈core q s i) : link q (core q s i) i j := by
  induction (aglow q).mp hj |>.2 with
  | refl => exact .refl
  | @tail k j h HH ih =>
    have hk : k∈core q s i := (aglow q).mpr ⟨HH.1,h⟩
    exact .tail (ih hk) ⟨hk,hj,HH.2.2⟩

lemma living {p : Finset I} (hp : p∈parts q s) : p⊆ s ∧ spark q p := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
  exact ⟨fun k hk => ((aglow q).mp hk).1,⟨i,(aglow q).mpr ⟨hi,.refl⟩⟩,fun _ hj _ hk =>
    ReflTransGen.trans (swap q (warm q hj)) (warm q hk)⟩
lemma owner {p : Finset I} (hp : p∈parts q s) (i : I) (hi : i∈p) : core q s i=p := by
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hp; exact (same q ((aglow q).mp hi).2).symm
lemma view {p r : Finset I} (hP : p∈parts q s) (hp : r∈parts q s) {i j : I} (hi : i∈p) (hj : j∈r) (ht : link q s i j) : p=r := by
  rw [← owner q hP i hi,← owner q hp j hj,same q ht]

lemma recombine (s : Finset I) : (parts q s).biUnion id=s := by
  ext i; constructor
  · intro h; obtain ⟨p,hp,h⟩ := mem_biUnion.mp h; exact (living q hp).1 h
  intro h; exact mem_biUnion.mpr ⟨_,mem_image_of_mem _ h, (aglow q).mpr ⟨h,.refl⟩⟩
variable [DecidableEq V] in
lemma separate (s : Finset I) : ((parts q s:Finset (Finset I)) : Set (Finset I)).PairwiseDisjoint (fun p => p.biUnion q) := by
  intro p hp r hr h
  apply disjoint_left.mpr; intro x hx he
  obtain ⟨i,h1,h2⟩ := mem_biUnion.mp hx; obtain ⟨j,h3,h4⟩ := mem_biUnion.mp he
  exact h (view q hp hr h1 h3 (.single ⟨(living q hp).1 h1,(living q hr).1 h3,x,h2,h4⟩))
lemma erases (s : Finset I) : (parts q s : Set (Finset I)).PairwiseDisjoint id := by
  intro p hp r hr hn
  exact disjoint_left.mpr fun _ hi hj => hn ((owner q hp _ hi).symm.trans (owner q hr _ hj))

omit [DecidableEq I] in
lemma flowing {W : Type*} {q' : I → Finset W} {s' : Finset I} (h : s ⊆ s')
    (hh : ∀ i∈s,∀ j∈s,meets q i j → meets q' i j) {i j} (he : link q s i j) : link q' s' i j :=
  ReflTransGen.mono (p:=bond q' s') (fun a b (hb : bond q s a b) =>
      ⟨h hb.1,h hb.2.1,hh a hb.1 b hb.2.1 hb.2.2⟩) _ _ he

/-- The tagged family is actually a component partition; restriction of
link on each member costs nothing. -/
lemma uncluttered [DecidableEq V] (S : Finset (Finset I)) (ht : (S : Set (Finset I)).PairwiseDisjoint (fun p => p.biUnion q))
    (hi : ∀ p∈S,spark q p) : parts q (S.biUnion id) = S := by
  let t := S.biUnion id
  have hq {p} (hp : p∈S) : p ⊆ t := fun i hi => mem_biUnion.mpr ⟨p,hp,hi⟩
  have he {p} (hp : p∈S) {i} (hx : i∈p) : core q t i=p := by
    have hr (j) (hj : link q t i j) : j∈p := by
      induction hj with
      | refl => exact hx
      | @tail k j _ hb IH =>
        obtain ⟨h1,h2,x,h3,h4⟩ := hb
        obtain ⟨D,hD,hd⟩ := mem_biUnion.mp h2
        by_cases h : p=D
        · exact h.symm ▸ hd
        exact False.elim ((disjoint_left.mp (ht hp hD h)) (mem_biUnion.mpr ⟨k,IH,h3⟩) (mem_biUnion.mpr ⟨j,hd,h4⟩))
    ext j; rw [aglow q]; constructor
    · rintro ⟨-,hz⟩; exact hr _ hz
    intro h; exact ⟨hq hp h, flowing q (hq hp) (fun _ _ _ _ => id) ((hi p hp).2 i hx j h)⟩
  ext p; rw [parts, mem_image]; constructor
  · rintro ⟨i,hh,rfl⟩; obtain ⟨D,hD,hz⟩ := mem_biUnion.mp hh; change core q t i∈S; rw [he hD hz]; exact hD
  intro hp; obtain ⟨i,h⟩ := (hi p hp).1
  exact ⟨i,hq hp h,he hp h⟩

omit [DecidableEq I] in
lemma spark_ac {n : Side} (X : I → Support n) (h : spark q s) (hv : ∀ i∈s,∀ j∈s,meets q i j→meets X i j) : Ac.Spark X s := by
  refine ⟨h.1,fun i hi j hj => ?_⟩
  have hx := flowing q (s':=s) Subset.rfl hv (h.2 _ hi _ hj)
  exact ReflTransGen.mono (p:=Ac.bonds X s) (fun _ _ (h : bond X s _ _) => ⟨h.1,h.2.1,h.2.2⟩) _ _ hx
end Collide

/-- Dual interaction. Marked-region interaction on every atom; actual
supersupport exclusion only on a complete hot block (forced or an off-mask
residual). -/
structure Kiln (I V S : Type*) where
  mention : I → Finset V
  wall : I → Finset S
  dirty : I → Prop

namespace Kiln
variable {I V W : Type*} (K : Kiln I V W)

def Hot (s : Finset I) (i : I) := ∃ j∈s,K.dirty j ∧ Collide.link K.mention s i j
def fuel (s : Finset I) (i : I) := (K.mention i).disjSum (if K.Hot s i then K.wall i else ∅)
abbrev Mole (s : Finset I) := Collide.spark (K.fuel s) s
variable [DecidableEq I] [DecidableEq V] [DecidableEq W]
abbrev slabs (s : Finset I) := Collide.parts (K.fuel s) s
open Collide
omit [DecidableEq I] [DecidableEq V] [DecidableEq W] in
lemma opens {i s} (h : K.dirty i) (hi : i∈s) : K.Hot s i := ⟨i,hi,h,.refl⟩

omit [DecidableEq I] [DecidableEq V] [DecidableEq W] in
@[simp] lemma fuel_left {i v s} : Sum.inl v∈K.fuel s i ↔ v∈K.mention i := by simp [fuel]
omit [DecidableEq I] [DecidableEq V] [DecidableEq W] in
@[simp] lemma fuel_right {i w s} : Sum.inr w∈K.fuel s i ↔ K.Hot s i ∧ w∈K.wall i := by by_cases h : K.Hot s i <;> simp [fuel,h]

omit [DecidableEq I] [DecidableEq V] [DecidableEq W] in
lemma increases {s : Finset I} {i j : I} (hx : link K.mention s i j) : link (K.fuel s) s i j :=
  flowing K.mention (s':=s) Subset.rfl (fun _ _ _ _ ⟨v,h,h'⟩ => ⟨Sum.inl v,(K.fuel_left).mpr h,(K.fuel_left).mpr h'⟩) hx

omit [DecidableEq V] [DecidableEq W] in
lemma hot_comp {p s : Finset I} (hp : p∈K.slabs s) (i : I) (hi : i∈p) : K.Hot p i ↔ K.Hot s i := by
  have h := (living (K.fuel s) hp).1
  constructor
  · rintro ⟨j,hj,H,ha⟩; exact ⟨j,h hj,H,flowing K.mention h (fun _ _ _ _ => id) ha⟩
  have he (j : I) (he : link K.mention s i j) : j∈p ∧ link K.mention p i j := by
    induction he with
    | refl => exact ⟨hi,.refl⟩
    | @tail b c hv hb ih =>
      have hj := K.increases (hv.tail hb)
      have hh : c∈p := by rw [← owner _ hp i hi]; exact (aglow (K.fuel s)).mpr ⟨hb.2.1,hj⟩
      exact ⟨hh,ih.2.tail ⟨ih.1,hh,hb.2.2⟩⟩
  rintro ⟨j,hj,hK,hE⟩
  exact ⟨j,(he j hE).1,hK,(he j hE).2⟩
omit [DecidableEq V] [DecidableEq W] in
lemma fuel_comp {p s : Finset I} (hp : p∈K.slabs s) (i : I) (hi : i∈p) : K.fuel p i = K.fuel s i := by unfold fuel; simp_rw [K.hot_comp hp i hi]
omit [DecidableEq V] [DecidableEq W] in
lemma good {p s : Finset I} (hp : p∈K.slabs s) : p⊆s ∧ K.Mole p := by
  obtain ⟨h,H1,H2⟩ := Collide.living (K.fuel s) hp
  refine ⟨h,H1,fun i hi j hj => Collide.flowing (K.fuel s) (s':=p) Subset.rfl (fun u hu v hv => ?_) (H2 i hi j hj)⟩
  unfold Collide.meets; rw [K.fuel_comp hp u hu,K.fuel_comp hp v hv]; exact id
omit [DecidableEq I] [DecidableEq V] [DecidableEq W] in
lemma tie {s : Finset I} {i j : I} (h : Collide.link (K.fuel s) s i j) (hi : K.Hot s i) : K.Hot s j := by
  induction h with
  | refl => exact hi
  | tail _ he ih =>
    obtain ⟨h1,h2,z,h3,h4⟩ := he
    cases z with
    | inl v =>
      obtain ⟨j,hj,H,ha⟩ := ih
      exact ⟨j,hj,H,.head ⟨h2,h1,v,(K.fuel_left).mp h4,(K.fuel_left).mp h3⟩ ha⟩
    | inr v => exact ((K.fuel_right).mp h4).1

def Takes (s : Finset I) := ∃ i∈s,K.dirty i
omit [DecidableEq I] [DecidableEq V] [DecidableEq W] in
lemma takes_mole {s : Finset I} (hp : K.Mole s) {i : I} (hi : i∈s) : K.Takes s ↔ K.Hot s i := by
  constructor
  · rintro ⟨j,hj,hh⟩; exact K.tie (hp.2 j hj i hi) (K.opens hh hj)
  rintro ⟨j,hj,ht,-⟩; exact ⟨j,hj,ht⟩

abbrev clubs (t : I → Finset V) (s : Finset I) := s.biUnion t
lemma clubs_away (s : Finset I) :
    (K.slabs s : Set (Finset I)).PairwiseDisjoint (clubs K.mention) := by
  intro p hp q hq hn; apply disjoint_left.mpr; intro v hv hx
  obtain ⟨i,hi,hv⟩ := mem_biUnion.mp hv
  obtain ⟨j,hj,hx⟩ := mem_biUnion.mp hx
  apply disjoint_left.mp (separate (K.fuel s) s hp hq hn)
    (mem_biUnion.mpr ⟨i,hi,(K.fuel_left).mpr hv⟩) (mem_biUnion.mpr ⟨j,hj,(K.fuel_left).mpr hx⟩)
lemma walls_away (s : Finset I) :
    ((K.slabs s).filter K.Takes : Set (Finset I)).PairwiseDisjoint (clubs K.wall) := by
  intro p hp q hq hn; rw [mem_coe,mem_filter] at hp hq
  apply disjoint_left.mpr; intro v hv hx
  obtain ⟨i,hi,hv⟩ := mem_biUnion.mp hv
  obtain ⟨j,hj,hx⟩ := mem_biUnion.mp hx
  have he {p i} (hp' : p∈K.slabs s) (hv' : K.Takes p) (hi : i∈p) := (K.hot_comp hp' i hi).mp ((K.takes_mole (K.good hp').2 hi).mp hv')
  apply disjoint_left.mp (separate (K.fuel s) s hp.1 hq.1 hn)
    (mem_biUnion.mpr ⟨i,hi,(K.fuel_right).mpr ⟨he hp.1 hp.2 hi,hv⟩⟩) (mem_biUnion.mpr ⟨j,hj,(K.fuel_right).mpr ⟨he hq.1 hq.2 hj,hx⟩⟩)

/-- Can undo and uniquely recover decomposition on output selections;
an inventory check is still needed, even here overlaps do NOT impose
mutual exclusion on the original K supports inside a Mole. -/
theorem undo (S : Finset (Finset I)) (h : ∀ p∈S,K.Mole p) (hv : (S:Set (Finset I)).PairwiseDisjoint (clubs K.mention))
    (hw : (↑(S.filter K.Takes) : Set (Finset I)).PairwiseDisjoint (clubs K.wall)) :
    K.slabs (S.biUnion id) = S := by
  let s := S.biUnion id
  have hx {p} (hp : p∈S) : p⊆s := fun i hi => mem_biUnion.mpr ⟨p,hp,hi⟩
  have he {p} (hp : p∈S) {i} (hi : i∈p) (j) (hj : link K.mention s i j) : j∈p := by
    induction hj with
    | refl => exact hi
    | @tail k j _ hb IH =>
      obtain ⟨h1,h2,x,h3,h4⟩ := hb; obtain ⟨D,hD,hd⟩ := mem_biUnion.mp h2
      by_cases H : p=D
      · exact H.symm ▸ hd
      exact False.elim ((disjoint_left.mp (hv hp hD H)) (mem_biUnion.mpr ⟨k,IH,h3⟩) (mem_biUnion.mpr ⟨j,hd,h4⟩))
  have ht (p) (hp : p∈S) (i : I) (hi : i∈p) : K.Hot s i ↔ K.Takes p := by
    constructor
    · rintro ⟨j,hj,hk,hr⟩; exact ⟨j,he hp hi j hr,hk⟩
    intro H; obtain ⟨j,hj,hk,hr⟩ := (K.takes_mole (h p hp) hi).mp H
    exact ⟨j,hx hp hj,hk,flowing K.mention (hx hp) (fun _ _ _ _ => id) hr⟩
  have hb (p) (hp : p∈S) (i) (hi : i∈p) : K.fuel s i = K.fuel p i := by
    unfold fuel; rw [ht _ hp _ hi,← K.takes_mole (h _ hp) hi]
  refine uncluttered (K.fuel s) S (fun p hp q hq hn => disjoint_left.mpr ?_) (fun p hp => ?_)
  · intro v he' ht'
    obtain ⟨i,hi,HS⟩ := mem_biUnion.mp he'; obtain ⟨j,hj,HT⟩ := mem_biUnion.mp ht'
    cases v with
    | inl v => exact disjoint_left.mp (hv hp hq hn) (mem_biUnion.mpr ⟨i,hi,(K.fuel_left).mp HS⟩) (mem_biUnion.mpr ⟨j,hj,(K.fuel_left).mp HT⟩)
    | inr v =>
      obtain ⟨hs,HS⟩ := (K.fuel_right).mp HS; obtain ⟨ht',HT⟩ := (K.fuel_right).mp HT
      exact disjoint_left.mp (hw (mem_filter.mpr ⟨hp,(ht p hp i hi).mp hs⟩) (mem_filter.mpr ⟨hq,(ht q hq j hj).mp ht'⟩) hn)
        (mem_biUnion.mpr ⟨i,hi,HS⟩) (mem_biUnion.mpr ⟨j,hj,HT⟩)
  refine ⟨(h _ hp).1,fun i hi j hj => flowing (K.fuel p) (s':=p) Subset.rfl (fun a ha b Hb => ?_) ((h p hp).2 i hi j hj)⟩
  unfold meets; rw [hb _ hp _ ha,hb _ hp _ Hb]; exact id

omit [DecidableEq I] [DecidableEq V] in
/-- One root/spanning estimate can pay a molecule, at overlap of
true projected footprints iff every marker mention includes its own new site
as required in grouping. -/
-- (Kiln interactions use no finset maps here)
theorem attends {n : Side} (K : Kiln I V (Site n)) (s : Finset I) (h : K.Mole s)
    (hX : ∀ i∈s,∀ j∈s,meets K.mention i j → meets K.wall i j) : Ac.Spark K.wall s := by
  refine spark_ac (K.fuel s) _ h (fun i hi j hj => ?_)
  rintro ⟨v,hv,hv'⟩
  cases v with
  | inl v => exact hX _ hi _ hj ⟨v,(K.fuel_left).mp hv,(K.fuel_left).mp hv'⟩
  | inr v => exact ⟨v,((K.fuel_right).mp hv).2,((K.fuel_right).mp hv').2⟩
end Kiln
end YM.Further.ShellBirth49.Fusing
