import YM.Corona.Fit
import YM.Next.RANK.Value
import YM.Work.H03



/-!
# Force at the correction level

Signed complex value-order history. Right letters attach when using a correction
(e^{-free connected}) on a failure of its indicated mask. Not one force per
cell; the alphabet can contain even within-cell overlaps. No independence. Every
surviving right letter must be adjacent to an old left via an actual tested flag;
require geometry of this meeting also for counting. Use true torus unions and
explicitly test flags again on resulting patches. Connected sets are finite,
nonrepeating labels. (`Work.H03` for techniques handling measured flags.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.EntryWord
open Lattice Wilson RG Finset MeasureTheory Marker Value Glyph
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type*} [DecidableEq V] [Fintype V] {ζ : V → Site n} {τ : ℝ}

structure Refusal (G : Gauge) (ζ : V → Site n) (τ : ℝ) where
  extent : Support n
  fires : modes V
  chosen : fires.val.Nonempty
  remembers i : i∈fires.val → ζ i∈ extent
  value : Config G n → ℂ
  meas : Measurable value
  refuses U : value U≠0 → ¬ Healthy τ extent U
  only : UsesFinal τ extent value
  inv : GaugeInvariant value

def Refusal.amount (H : Refusal G ζ τ) (U) := Poly.send H.fires (H.value U)

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable (K : ι → Lifted G ζ τ) (F : κ → Refusal G ζ τ)

def area (x : ι ⊕ κ) := Sum.elim (fun i => (K i).extent) (fun j => (F j).extent) x
def mode (x : ι ⊕ κ) := Sum.elim (fun i => (K i).fires) (fun j => (F j).fires) x
def score (x : ι ⊕ κ) := Sum.elim (fun i => (K i).value) (fun j => (F j).value) x
def hook (x : ι ⊕ κ) (U : Config G n) := Poly.send (mode K F x) (score K F x U)

-- Lefts still evaluated with their original constraints

def grabs (s : Finset (ι ⊕ κ)) := ∀ j∈s.toRight, ∃ i∈s.toLeft, ¬ Disjoint (K i).extent (F j).extent
def locks (s : Finset (ι ⊕ κ)) := Ac.Spark (area K F) s ∧ s.toLeft.Nonempty ∧
  (s.toLeft:Set ι).PairwiseDisjoint (fun i => (K i).extent) ∧ grabs K F s
abbrev Latch := {s // locks K F s}
def keep (p : Latch K F) := p.val.biUnion (area K F)
def owns (p : Latch K F) := p.val.toLeft.biUnion (fun i => (K i).inventory)
def taps (p : Latch K F) := scene (p.val.biUnion (fun i => (mode K F i).val))
def cube (s : Finset (ι ⊕ κ)) (U : Config G n) := ∏ i ∈ s,hook K F i U

omit [DecidableEq ι] [DecidableEq κ]
lemma held (p : Latch K F) : owns K F p ⊆ keep K F p := by
  intro x hx; obtain ⟨i,hi,h⟩ := mem_biUnion.mp hx; exact mem_biUnion.mpr ⟨.inl i, mem_toLeft.mp hi,(K i).records h⟩
lemma has (p : Latch K F) : (owns K F p).Nonempty := by
  obtain ⟨i,hi⟩ := p.property.2.1; obtain ⟨x,hx⟩ := (K i).needed; exact ⟨x,mem_biUnion.mpr ⟨i,hi,hx⟩⟩
lemma visible (p : Latch K F) (i : V) (hx : i∈ (taps K F p).val) : ζ i∈ keep K F p := by
  obtain ⟨x,hh,hp⟩ := mem_biUnion.mp hx
  refine mem_biUnion.mpr ⟨x,hh,?_⟩
  cases x with
  | inl x => exact (K x).remembers i hp
  | inr x => exact (F x).remembers i hp

-- prove measurability per part: don't even require a BorelSpace instance on Poly.
private lemma tint {s : Finset (ι ⊕ κ)} (i : modes V) : Measurable fun U => (cube K F s U).part i := by
  induction s using Finset.induction_on generalizing i with
  | empty => simpa only [cube,prod_empty] using measurable_const
  | @insert a s ha ih =>
    simp only [cube,prod_insert ha]
    change Measurable fun U => ((hook K F a U)*(cube K F s U)).part i
    simp_rw [hook,plate]; split
    · apply Measurable.mul _ (ih _)
      cases a with
      | inl a => exact (K a).meas
      | inr a => exact (F a).meas
    exact measurable_const

private lemma coloured (s : Finset (ι ⊕ κ)) (U : Config G n) :
    ∃ z, cube K F s U=Poly.send (scene (s.biUnion fun i => (mode K F i).val)) z := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by rw [cube,prod_empty,biUnion_empty]; rfl⟩
  | @insert a b ha ih =>
    rw [biUnion_insert,cube,prod_insert ha]
    obtain ⟨z,hz⟩ := ih; unfold cube at hz
    rw [hz,hook,plate_pair]; split
    · exact ⟨_,rfl⟩
    exact ⟨0,(Poly.send_zero ..).symm⟩
lemma cube_at (p : Latch K F) (U : Config G n) :
    Poly.send (taps K F p) ((cube K F p.val U).part (taps K F p))=cube K F p.val U := by
  obtain ⟨z,hz⟩ := coloured K F p.val U; change cube K F p.val U=Poly.send (taps K F p) z at hz; rw [hz]; simp

private def inside (p : Latch K F) (U : Config G n) := keep K F p ∩ flags τ U=owns K F p
private lemma within_bounds (p : Latch K F) : MeasurableSet {U | inside K F p U} := by
  rw [show {U | inside K F p U} = ⋃ s : {q : Support n // keep K F p ∩ q=owns K F p}, {U | flags τ U=s.val} by
    ext i; simp only [Set.mem_setOf_eq,Set.mem_iUnion]; constructor
    · exact fun H => ⟨⟨_,H⟩,rfl⟩
    rintro ⟨s,h⟩; rw [inside,h]; exact s.property]
  exact MeasurableSet.iUnion fun _ => flags_measurable_eq ..

private lemma sees (p : Latch K F) : UsesFinal τ (keep K F p) (cube K F p.val) := by
  intro U u hu hp
  refine prod_congr rfl fun i hi => congr_arg (Poly.send (mode K F i)) ?_
  have he : UsesFinal τ (area K F i) (score K F i) := by
    cases i with
    | inl i => exact (K i).only
    | inr j => exact (F j).only
  exact Work.H03.reads_larger (fun x hx => mem_biUnion.mpr ⟨i,hi,hx⟩) he _ _ hu hp

private lemma turns (p : Latch K F) (k : Site n → G.El) (U : Config G n) : cube K F p.val (gauge k U)=cube K F p.val U := by
  apply Finset.prod_congr rfl
  intro i _; apply congr_arg (Poly.send _)
  cases i with
  | inl i => exact (K i).inv k U
  | inr j => exact (F j).inv k U

def merged (p : Latch K F) : Lifted G ζ τ where
  extent := keep K F p
  inventory := owns K F p
  needed := has K F p
  records := held K F p
  fires := taps K F p
  remembers := visible K F p
  value := fun U => if inside K F p U then (cube K F p.val U).part (taps K F p) else 0
  meas := Measurable.ite (within_bounds K F p) (tint K F _) measurable_const
  flag U := by by_cases h : inside K F p U; exact fun _ => h; simp only [if_neg h,ne_eq,not_true,false_imp_iff]
  only := by
    intro U V h1 h2; simp only [inside, sees K F p U V h1 h2,h2]; split_ifs <;> rfl
  inv := by intro k U; simp only [turns K F p, inside,gauge_flags]; split_ifs <;> rfl

lemma look_inside (p : Latch K F) (U : Config G n) :
    (merged K F p).amount U= if keep K F p ∩ flags τ U = owns K F p then cube K F p.val U else 0 := by
  unfold merged Lifted.amount inside
  simp only
  split_ifs
  · exact cube_at K F p U
  exact Poly.send_zero ..

-- Quiet word when moving masks at CURRENT threshold. Add any number of
-- partners, each one nonempty-marked. Thus quiet Latch must be one old K,
-- and we really preserve the labelled vacuum options (including zero).
def monoWord (j : ι) : Latch K F := by
  let S : Finset (ι ⊕ κ):= {.inl j}
  have h1:S.toLeft={j}:=by ext i;simp [S]
  have h2:S.toRight=∅:=by ext i;simp [S]
  have H:S.Nonempty:= singleton_nonempty _
  refine ⟨S,⟨H,fun a ha b hb=>?_⟩,h1.symm ▸ singleton_nonempty _,?_,?_⟩
  · obtain rfl:= mem_singleton.mp ha; obtain rfl:=mem_singleton.mp hb;exact .refl
  · rw [h1,Finset.coe_singleton]; exact Set.pairwiseDisjoint_singleton ..
  intro j hj; rw [h2] at hj; exact False.elim (notMem_empty j hj)
lemma corresponding (p : Latch K F) (h : taps K F p = quiet V): ∃ j,p=monoWord K F j:= by
  let v:=p.val
  have hR {b : Prop} : ∀ i : κ, Sum.inr i ∈ v → b := by
    intro i hr; obtain ⟨x,hx⟩:= (F i).chosen
    have hf:x∈ v.biUnion fun a=> (mode K F a).val:= mem_biUnion.mpr ⟨.inr i,hr,hx⟩
    exact False.elim (notMem_empty x (show x∈(quiet V).val from h ▸ (show x∈(taps K F p).val from hf)))
  obtain ⟨i,hi⟩:=p.property.2.1
  have hp:Sum.inl i ∈ v:= mem_toLeft.mp hi
  refine ⟨i,Subtype.ext ?_⟩
  change v={Sum.inl i}
  ext j; rw [mem_singleton]; constructor
  · intro hx
    have he a (h:Ac.chain (area K F) v (Sum.inl i) a) : a=Sum.inl i:= by
      induction h with
      | refl=> rfl
      | @tail b a h hv hh=>
        cases a with
        | inr j=>exact hR _ hv.2.1
        | inl j=>
          subst b
          by_contra he
          have hD:= p.property.2.2.1 hi (mem_toLeft.mpr hv.2.1) (fun h=> he (congr_arg Sum.inl h.symm))
          obtain ⟨x,hx,hh⟩:= hv.2.2
          exact Finset.disjoint_left.mp hD hx hh
    exact he _ (p.property.1.2 _ hp _ hx)
  rintro rfl; exact hp
lemma mono_key (j) (U : Config G n) :
    let v:=merged K F (monoWord K F j)
    v.extent=(K j).extent∧ v.inventory=(K j).inventory∧v.fires=(K j).fires∧v.value U=(K j).value U:= by
  intro v; let X:=monoWord K F j
  have h : X.val={Sum.inl j}:=rfl
  have he:X.val.toLeft={j}:=by ext;simp [h]
  have hl: keep K F X=(K j).extent:= by rw [keep,h,singleton_biUnion];rfl
  have hr: owns K F X=(K j).inventory:= by rw [owns,he,singleton_biUnion]
  have hk: taps K F X=(K j).fires:=by rw [taps,h,singleton_biUnion];rfl
  refine ⟨hl,hr,hk,?_⟩
  change (merged K F X).value _=_
  dsimp only [merged]; rw [hk,cube,h,prod_singleton]
  split
  · change (Poly.send (K j).fires _).part _=_; rw [Poly.part_send,if_pos rfl]; rfl
  rename_i hX
  symm; apply Classical.byContradiction; intro hh; apply hX; unfold inside; rw [hl,hr]; exact (K j).flag U hh
lemma monogous [Fintype ι] [Fintype κ] (i) (U) : column (merged K F) i U=column K i U:= by
  unfold column
  let S:=(univ (α:=ι)).image (monoWord K F)
  rw [← Finset.sum_subset (subset_univ S),Finset.sum_image]
  · apply Finset.sum_congr rfl; intro j _; obtain ⟨h,H,h₁,h₂⟩:=mono_key K F j U
    rw [h,H,h₁,h₂]
  · intro a ha b hb hv
    have hx := congr_arg Subtype.val hv
    change ({Sum.inl a} : Finset (ι ⊕ κ))={Sum.inl b} at hx; simpa using hx
  intro a ha hn
  split
  · rename_i h; obtain ⟨j,hj⟩:= corresponding K F a h.1
    exact False.elim (hn (mem_image.mpr ⟨j,mem_univ _,hj.symm⟩))
  rfl
end YM.Next.Rank.EntryWord
