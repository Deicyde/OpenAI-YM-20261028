import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Layout
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.TiltField

/-! # Compiler of the first-system inventory BEFORE marked log

Use through `Matric`. Layout keeps actual touch-neighborhoods (e.g.
Freezing, W masks including halos, ancestors/K alignment). Entries require
microscopic Sees and supports proof; don't simply assume that after-
Assembly reads are local. `luminous` & companions make overlap
components (Clubs). Fine vs coarse support/inventory ledgers separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Filter MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x τ : ℝ} {F : Orchard S} {T : Tube G S} {A : Stores S}
    {P : Teller G} {k : Streak F} {V : Config G c}
    {W ι : Type} [Fintype W] [DecidableEq W] {u : W → Site c}

structure PaintCan (S : StepData c f) (G : Gauge) (x : ℝ) (F : Orchard S) (u : W → Site c) (τ : ℝ) where
  X : Support c
  goal : Support c
  supplies : Support f
  wants : Support f
  barricade : Support c -- belongs here at coarse level
  encumbrance : Support f -- pre-output K list
  permit : vouchers S
  hues : modes W
  lamp : Shader G S x F ℂ
  exists_site : X.Nonempty
  go : goal ⊆ X
  store i : i∈supplies → S.ratio.parent i∈X -- from unmarked estimation (Zest)
  feeds i : i∈wants → S.ratio.parent i∈X -- to license input K labels
  coverage : barricade ⊆ X
  embeds i : i∈encumbrance → S.ratio.parent i ∈ X
  lends : wards permit ⊆ X
  remembers i : i∈hues.val→ u i∈X
  sees : Sees lamp X goal.Nonempty τ

namespace Display
variable (Q : ι→ PaintCan S G x F u τ)
abbrev zones (i) := (Q i).X
def premise (s : Finset ι) := (s:Set ι).PairwiseDisjoint (fun i=>(Q i).barricade) ∧
    (s:Set ι).PairwiseDisjoint (fun i=>(Q i).encumbrance) ∧ s.biUnion (fun i=> (Q i).supplies)=s.biUnion (fun i=> (Q i).wants)
def enlist (s : Finset ι) := premise Q s ∧ (s:Set ι).PairwiseDisjoint (fun i=>(Q i).hues.val)

abbrev Club := {s : Finset ι // Spark (zones Q) s ∧ enlist Q s}
def zone (s : Club Q) := s.val.biUnion (zones Q)
def cardGoal (s : Finset ι) := s.biUnion (fun i=>(Q i).goal)
def glow (s : Finset ι) := s.sup (fun i=>(Q i).permit)
def fires (s : Finset ι) : modes W := scene (s.biUnion fun i=>(Q i).hues.val)
def stage (s : Finset ι) : Shader G S x F ℂ := fun A k U z=> ∏ i∈s,(Q i).lamp A k U z
lemma observer (s : Club Q) : Sees (stage Q s.val) (zone Q s) (cardGoal Q s.val).Nonempty τ := by
  refine Sees.cake s.val fun i hi=> (Q i).sees.larger ?_ ?_
  exact fun _ hb=> mem_biUnion.mpr ⟨_,hi,hb⟩
  rintro ⟨p,hp⟩; exact ⟨p,mem_biUnion.mpr ⟨_,hi,hp⟩⟩
lemma has (s : Club Q) : (zone Q s).Nonempty:= by
  obtain ⟨i,hi⟩:= s.property.1.1; exact (Q i).exists_site.mono fun p hp=>mem_biUnion.mpr ⟨_,hi,hp⟩
lemma goalZone (s : Club Q) : cardGoal Q s.val ⊆ zone Q s := by
  intro i hi; obtain ⟨x,hx,h⟩:=mem_biUnion.mp hi;exact mem_biUnion.mpr ⟨_,hx,(Q x).go h⟩
lemma knows (s : Club Q) (i : W)(hp : i∈(fires Q s.val).val) : u i∈zone Q s:= by obtain ⟨j,hj,h⟩:=mem_biUnion.mp hp; exact mem_biUnion.mpr ⟨j,hj,(Q j).remembers i h⟩
def validArea (s : Club Q) (U : Config G c) := zone Q s∩flags τ U=cardGoal Q s.val
lemma measured (s : Club Q) : MeasurableSet {U | validArea Q s U}:= by
  let P:= {u : Support c//zone Q s∩u=cardGoal Q s.val}
  rw [show {U|validArea Q s U} = ⋃ i : P,{U : Config G c|flags τ U=i.val} by
    ext V; simp only [Set.mem_setOf_eq,Set.mem_iUnion]; constructor
    · intro h; exact ⟨⟨_,h⟩,rfl⟩
    rintro ⟨i,h⟩; rw [validArea,h]; exact i.property]
  exact MeasurableSet.iUnion fun i => flags_measurable_eq ..

variable [DecidableEq ι]
def draw (r : Finset (Club Q)) := r.biUnion Subtype.val
lemma drawn_marks (r : Finset (Club Q)) : cardGoal Q (draw Q r)=r.biUnion (fun i=>cardGoal Q i.val):= by ext; simp [cardGoal,draw]; grind
lemma drew (p : Finset (Club Q)) (h : (p:Set _).PairwiseDisjoint (zone Q)) : enlist Q (draw Q p):= by
  let a:=draw Q p
  have skins {O : Type} [DecidableEq O] (S : ι→Finset O) (q : O → Site c) (hh : ∀ i,∀ j∈S i,q j∈ (Q i).X)
      (he : ∀ i:Club Q,(i.val:Set _).PairwiseDisjoint S): (a:Set _).PairwiseDisjoint S:= by
    intro i hi j hj heq; obtain ⟨v,hv,hV⟩:=mem_biUnion.mp hi; obtain ⟨t,ht,hT⟩:=mem_biUnion.mp hj
    rcases eq_or_ne v t with g|g; subst t;exact he _ hV hT heq
    exact Finset.disjoint_left.mpr fun x hx hm=> Finset.disjoint_left.mp (h hv ht g) (Finset.mem_biUnion.mpr ⟨_,hV,hh i x hx⟩) (mem_biUnion.mpr ⟨_,hT,hh j x hm⟩)
  refine ⟨⟨skins (fun i=>(Q i).barricade) id (fun i _ hz=> (Q i).coverage hz
      ) (fun k=> k.property.2.1.1), skins (fun i=>(Q i).encumbrance) S.ratio.parent (fun i=>(Q i).embeds) (fun k=>k.property.2.1.2.1),?_⟩, skins _ u (fun i=>(Q i).remembers) (fun k=>k.property.2.2)⟩
  have hz (F : ι → Support f) : (draw Q p).biUnion F=p.biUnion fun t=> t.val.biUnion F:= by ext; simp [draw]; grind
  simp_rw [hz]; exact Finset.biUnion_congr rfl fun i _=> i.property.2.1.2.2

lemma luminous (p : Finset ι) (h : enlist Q p) : ∃ s : Finset (Club Q), (s:Set (Club Q)).PairwiseDisjoint (zone Q) ∧ draw Q s=p:= by
  let A:=Parts (zones Q) p; let v:= A.preimage (Subtype.val : Club Q → Finset ι) Subtype.val_injective.injOn
  have hx i (hi:i∈A) : enlist Q i := by
    have he := (lives (zones Q) p hi).1
    refine ⟨⟨fun j hj k hk hz=>h.1.1 (he hj) (he hk) hz, fun j hj k hk hz=>h.1.2.1 (he hj) (he hk) hz,?_⟩, fun j hj k hk hz=>h.2 (he hj) (he hk) hz⟩
    have ha (u w : ι→Support f) (H : p.biUnion u=p.biUnion w) (ht : ∀ j,∀ x∈u j,S.ratio.parent x∈(Q j).X) (hw : ∀ j,∀ x∈w j,S.ratio.parent x∈(Q j).X) : i.biUnion u ⊆ i.biUnion w:= by
      intro x hv; obtain ⟨j,hj,hx⟩:=mem_biUnion.mp hv
      obtain ⟨y,hy,hh⟩:=mem_biUnion.mp (show x∈p.biUnion w from H ▸ (mem_biUnion.mpr ⟨_,he hj,hx⟩:x∈p.biUnion u))
      apply mem_biUnion.mpr; rw [← Ac.contains (zones Q) hi j hj]
      exact ⟨y,(Ac.bright ..).2 ⟨hy,.single ⟨he hj,hy,S.ratio.parent x,ht _ _ hx,hw _ _ hh⟩⟩,hh⟩
    exact Finset.Subset.antisymm (ha _ _ h.1.2.2 (fun j=>(Q j).store) (fun j=>(Q j).feeds)) (ha _ _ h.1.2.2.symm (fun j=>(Q j).feeds) (fun j=>(Q j).store))
  have hh : v.image Subtype.val=A:= by
    ext i; constructor
    · intro h; obtain ⟨i,hi,rfl⟩:=mem_image.mp h; exact mem_preimage.mp hi
    intro h; exact mem_image.mpr ⟨(⟨i,(lives (zones Q) p h).2,hx i h⟩:Club Q), mem_preimage.mpr h,rfl⟩
  refine ⟨v,fun i hi j hj he=>Ac.separate (zones Q) p (mem_preimage.mp hi) (mem_preimage.mp hj) (mt Subtype.ext he),?_⟩
  rw [show draw Q v=(v.image Subtype.val).biUnion id from Finset.ext fun a=>by simp [draw],hh]; exact reconstruct (zones Q) p

lemma recovered {p : Finset (Club Q)} (h : (p:Set _).PairwiseDisjoint (zone Q)) : Parts (zones Q) (draw Q p)=p.image Subtype.val:= by
  rw [show draw Q p=(p.image Subtype.val).biUnion id from Finset.ext fun a=>by simp [draw]]
  refine Ac.separates (zones Q) _ ?_ ?_
  · intro i hi; obtain ⟨i,_,rfl⟩:=mem_image.mp hi; exact i.property.1
  intro i hi j hj hh; obtain ⟨i,hI,rfl⟩:=mem_image.mp hi; obtain ⟨j,hJ,rfl⟩:=mem_image.mp hj
  exact h hI hJ (fun h=>hh (congr_arg _ h))
omit [DecidableEq ι] in
lemma autonomy {p : Finset (Club Q)} (h : (p:Set (Club Q)).PairwiseDisjoint (zone Q)) : (p:Set (Club Q)).PairwiseDisjoint Subtype.val := by
  intro i hi j hj hp; apply Finset.disjoint_left.mpr; intro x ha hb
  obtain ⟨x,hx⟩:=(Q x).exists_site; exact Finset.disjoint_left.mp (h hi hj hp) (mem_biUnion.mpr ⟨_,ha,hx⟩) (mem_biUnion.mpr ⟨_,hb,hx⟩)
lemma zone_pass {s : Finset (Club Q)} (h : (s:Set _).PairwiseDisjoint (zone Q)) (hp : cardGoal Q (draw Q s)= flags τ V) (t : Club Q) (ht : t∈s) : validArea Q t V:= by
  unfold validArea; rw [← hp, drawn_marks]; ext i; rw [Finset.mem_inter]; constructor
  · rintro ⟨hi,hk⟩; obtain ⟨x,hx,he⟩:=mem_biUnion.mp hk; rcases eq_or_ne x t with v|v; subst x; exact he
    exact False.elim (Finset.disjoint_left.mp (h hx ht v) (goalZone Q _ he) hi)
  intro hi; exact ⟨goalZone Q _ hi,mem_biUnion.mpr ⟨_,ht,hi⟩⟩

lemma cost_bundled (p : Finset ι) : wards (glow Q p)=p.biUnion fun i=> wards (Q i).permit:= by
  induction p using Finset.induction_on with
  | empty=>ext; simp [glow,wards]
  | insert i a h ih=>
    rw [glow,sup_insert,biUnion_insert,← ih]
    change wards (S:=S) ((Q i).permit ⊔ glow Q a)=_
    generalize (Q i).permit=v; generalize glow Q a=w
    unfold wards; change (v.1∪w.1).biUnion (startPos S)∪(v.2∪w.2).biUnion pinPos=_ -- use coercion
    rw [Finset.union_biUnion, Finset.union_biUnion]; ac_rfl
lemma windings (q : Finset (Club Q)) (t : Club Q) (h : t∈q) (hp : (q:Set _).PairwiseDisjoint (zone Q)) (V : Config G c) (k : Streak F) :
    Nearby (zone Q t) V V (stapled x (glow Q t.val) V) (stapled x (glow Q (draw Q q)) V) k k := by
  let A:= draw Q (q.erase t)
  have hC:glow Q (draw Q q) = glow Q t.val ⊔ glow Q A:= by
    unfold glow draw A
    nth_rewrite 1 [← insert_erase h]; rw [biUnion_insert, sup_union]; rfl
  rw [hC]; apply towards
  rw [cost_bundled]; apply Finset.disjoint_left.mpr; intro a hi he
  obtain ⟨j,hj,h⟩:=mem_biUnion.mp he; obtain ⟨t',ht',hv⟩:=mem_biUnion.mp hj
  exact Finset.disjoint_left.mp (hp (show _ from ‹t∈q›) (mem_erase.mp ht').2 (mem_erase.mp ht').1.symm) hi (mem_biUnion.mpr ⟨j,hv,(Q j).lends h⟩)
end Display
end YM.PhysicalNext.InteractingRank
