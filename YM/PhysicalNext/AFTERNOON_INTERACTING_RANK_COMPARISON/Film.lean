import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Gallery

/-!
# Restore the same unmarked projection chart

Match by actual Embeddings. Now can feed Flux.Vac data once supplied
on a smaller (e.g. mark-free) alphabet, to generate obligations on
the *whole* palette. Don't ask to reevaluate E# on different H or B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision Relation
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x τ : ℝ} {F : Orchard S} {T : Tube G S}
    {P : Teller G} {W ι κ : Type} [Fintype W] [DecidableEq W] {u : W → Site c}
    {Q : ι→ PaintCan S G x F u τ} {R : κ → PaintCan S G x F u τ}
structure Film (X : ι↪κ) (Q : ι→PaintCan S G x F u τ) (R : κ→PaintCan S G x F u τ) : Prop where
  knows i : Q i=R (X i)
variable {X : ι↪κ}
lemma casts {n : Side} {κ Y : Type*} (p : κ↪Y) (S : κ→Support n) (T : Y→Support n) (s : Finset κ) (H : ∀ i,S i=T (p i)) : Spark S s ↔ Spark T (s.map p):= by
  constructor
  · intro h; refine ⟨Finset.map_nonempty.mpr h.1,fun b hb c hc=>?_⟩
    obtain ⟨i,hi,rfl⟩:=Finset.mem_map.mp hb; obtain ⟨j,hj,rfl⟩:=Finset.mem_map.mp hc
    refine ReflTransGen.lift p ?_ i j (h.2 i hi j hj); rintro a b ⟨hu,hv,i,H',he'⟩
    exact ⟨mem_map.mpr ⟨a,hu,rfl⟩,mem_map.mpr ⟨b,hv,rfl⟩,i,H _ ▸ H',H _ ▸ he'⟩
  intro h
  refine ⟨Finset.map_nonempty.mp h.1,fun i hi j hj=>?_⟩
  have hp b (h': chain T (s.map p) (p i) b) : ∃ k∈s, p k=b∧chain S s i k:= by
    induction h' with
    | refl=> exact ⟨_,hi,rfl,.refl⟩
    | @tail a b _ Hv Hs=>
      obtain ⟨k,hk,rfl,ht⟩:=Hs; obtain ⟨-,hv,j,hj,hb⟩:=Hv; obtain ⟨y,hy,rfl⟩ := mem_map.mp hv
      exact ⟨y,hy,rfl,.tail ht ⟨hk,hy,j,H k|>.symm ▸ hj,H y|>.symm ▸ hb⟩⟩
  obtain ⟨v,_,hx,he⟩:=hp (p j) (h.2 _ (mem_map.mpr ⟨_,hi,rfl⟩) _ (mem_map.mpr ⟨_,hj,rfl⟩)); exact p.injective hx ▸ he
lemma filming {κ Y α : Type*} [DecidableEq α] (p : κ↪Y) (S : κ→Finset α) (T : Y→Finset α) (s : Finset κ) (H : ∀ i,S i=T (p i)) :
    s.biUnion S=(s.map p).biUnion T := by ext; simp [H]
lemma viewers {κ Y α : Type*} (p : κ↪Y) (S : κ→Finset α) (T : Y→Finset α) (s : Finset κ) (H : ∀ i,S i=T (p i)) :
    (s:Set κ).PairwiseDisjoint S ↔ (s.map p:Set Y).PairwiseDisjoint T := by
  constructor
  · intro h i hi j hj hp; obtain ⟨v,hv,rfl⟩:=mem_map.mp hi; obtain ⟨w,hw,rfl⟩:=mem_map.mp hj
    change Disjoint (T (p v)) (T (p w))
    exact H v ▸ H w ▸ (show Disjoint (S v) (S w) from h hv hw (fun h=>hp (congr_arg _ h)))
  intro h i hi j hj he
  change Disjoint (S i) (S j)
  rw [H,H]; exact h (mem_map.mpr ⟨_,hi,rfl⟩) (mem_map.mpr ⟨_,hj,rfl⟩) (p.injective.ne he)
lemma frames {κ Y : Type} (p : κ↪Y) (S : κ→Support c) (T : Y→Support c) (s : Finset κ) (H : ∀ i,S i=T (p i))
    (v : κ → Glyph.veil W) (w : Y→ Glyph.veil W) (h : ∀ i,v i=w (p i)) : Flux.chair S v s=Flux.chair T w (s.map p):= by
  unfold Flux.chair; rw [show (s.map p).powerset = s.powerset.map ((Finset.mapEmbedding p).toEmbedding) from ?_,Finset.sum_map]
  · apply Finset.sum_congr rfl; intro i _
    change _=(if Flux.packed T (i.map p) then _ else _)
    simp only [Flux.packed,← viewers p _ _ _ H]; split_ifs <;> first|rfl|skip
    change _=∏ i∈i.map p,w i; rw [Finset.prod_map]; exact Finset.prod_congr rfl fun i _=>h i
  symm; apply Finset.eq_of_subset_of_card_le
  intro i hi; obtain ⟨i,hI,rfl⟩:=mem_map.mp hi; exact mem_powerset.mpr (map_subset_map.mpr (mem_powerset.mp hI))
  simp

namespace Film
variable (h : Film X Q R)
include h
lemma paid (s : Finset ι) : enlist Q s ↔ enlist R (s.map X):= by
  unfold enlist premise
  rw [viewers X (fun i=>(Q i).barricade) (fun i=>(R i).barricade) s (fun i=>congr_arg _ (h.knows i)),
    viewers X (fun i=>(Q i).encumbrance) (fun i=>(R i).encumbrance) s (fun i=>congr_arg _ (h.knows i)),
    filming X (fun i=>(Q i).supplies) (fun i=>(R i).supplies) s (fun i=>congr_arg _ (h.knows i)),
    filming X (fun i=>(Q i).wants) (fun i=>(R i).wants) s (fun i=>congr_arg _ (h.knows i))]
  exact and_congr Iff.rfl (viewers X _ _ _ fun i=>congr_arg (fun a=>(PaintCan.hues a).val) (h.knows i))
lemma projector (s : Finset ι) : Spark (zones Q) s ↔ Spark (zones R) (s.map X):= casts X _ _ s (fun i=> congr_arg _ (h.knows i))
def club : Club Q ↪ Club R where
  toFun s := ⟨s.val.map X,(h.projector _).mp s.property.1, (h.paid _).mp s.property.2⟩
  inj' _ _ he:= Subtype.ext ((Finset.map_injective X) (congr_arg Subtype.val he))
lemma areas (s : Club Q) : zone Q s=zone R (h.club s) := filming X _ _ _ (fun i=> congr_arg _ (h.knows i))
lemma dues (s : Club Q) : cardGoal Q s.val=cardGoal R (h.club s).val:= filming X _ _ _ (fun i=> congr_arg _ (h.knows i))
lemma fired (s : Club Q) : fires Q s.val=fires R (h.club s).val:= congr_arg scene (filming X _ _ s.val fun i=> congr_arg (fun a=>(PaintCan.hues a).val) (h.knows i))
lemma beams (s : Club Q) : promotes Q s ↔ promotes R (h.club s) := by unfold promotes; rw [h.dues,h.fired]
lemma portal (s) : validArea Q s=validArea R (h.club s):= by funext v; unfold validArea; rw [h.areas,h.dues]
lemma letter_bill (s) : letter Q (T:=T) s=letter R (T:=T) (h.club s):= by
  unfold letter; change glance _ _ _=glance _ (stage R (s.val.map X)) (glow R (s.val.map X))
  congr 1
  · funext a b c d; unfold stage; rw [Finset.prod_map]; exact Finset.prod_congr rfl fun i _ => congr_arg (fun l=> PaintCan.lamp l a b c d) (h.knows i)
  unfold glow; rw [Finset.sup_map]; apply Finset.sup_congr rfl;intro i _; exact congr_arg _ (h.knows i)
def differs : Inn Q↪ Inn R where
  toFun s := ⟨h.club s.val,(h.beams _).1 s.property⟩
  inj' _ _ H:= Subtype.ext (h.club.injective (congr_arg Subtype.val H))
lemma movie (s : Inn Q) (ht : Boosted T P x) : bequeath Q ht s=bequeath R ht (h.differs s):= by
  have hp := h.dues s.val
  have hv i : validArea Q s.val i ↔ validArea R (h.club s.val) i:= Iff.of_eq (congr_fun (h.portal _) i)
  unfold bequeath; dsimp only [differs, Function.Embedding.coeFn_mk]
  split_ifs with h₁ h₂ h₂
  · apply congr_arg; apply li (h.areas _) hp (h.fired _)
    funext i; unfold foundering; dsimp only; rw [h.letter_bill]; split_ifs <;> grind
  · exact False.elim (h₂ (hp ▸ h₁))
  · exact False.elim (h₁ (hp.symm ▸ h₂))
  apply congr_arg; exact pr (h.areas _) (h.fired _) (h.letter_bill _)
where
  li {A B : Lifted G u τ} (h : A.extent=B.extent) (hp : A.inventory=B.inventory) (hf : A.fires=B.fires) (hv : A.value=B.value) : A=B:=by cases A;cases B;congr
  pr {A B : SourceAt G u} (h : A.extent=B.extent) (hf : A.fires=B.fires) (hv : A.value=B.value) : A=B:=by cases A;cases B;congr

def free : Exe Q ↪ Exe R where
  toFun s:=⟨h.club s.val,mt (h.beams _).mpr s.property⟩
  inj' _ _ H:= Subtype.ext (h.club.injective (congr_arg Subtype.val H))
lemma free_bill (s : Exe Q) (ht : Boosted T P x) : germ Q ht s=germ R ht (h.free s):= inner_ext (h.areas _) (h.fired _) (h.letter_bill _)
where
  inner_ext {A B : Inner G u} (h : A.extent=B.extent) (hf : A.fires=B.fires) (hp : A.value=B.value) : A=B:=by cases A;cases B;congr

lemma backroll (s : Club R) (hq : ∀ i ∈ s.val,i ∈ Set.range X) : ∃ t : Club Q,h.club t=s:= by
  let a:=s.val.preimage X X.injective.injOn
  have he : a.map X=s.val:= by
    ext i; constructor
    · intro ht; obtain ⟨j,hj,rfl⟩:=mem_map.mp ht; exact mem_preimage.mp hj
    intro hf; obtain ⟨x,rfl⟩:=hq i hf; exact mem_map.mpr ⟨_,mem_preimage.mpr hf,rfl⟩
  have hs : Spark (zones Q) a ∧ enlist Q a:= by rw [projector h, paid h,he]; exact s.property
  exact ⟨⟨_,hs⟩,Subtype.ext he⟩
variable (hq : ∀ i,(R i).hues=quiet W → i ∈ Set.range X)
include hq in
lemma backed (s : Club R) (hp : fires R s.val=quiet W) : s∈Set.range h.club:= h.backroll s (fun i hi=> hq i (Subtype.ext (Finset.subset_empty.mp (fun j hj => (show j∈(quiet W).val from hp ▸ (show j∈(fires R s.val).val from Finset.mem_biUnion.mpr ⟨_,hi,hj⟩))))))
include hq in
lemma renewal (s : Exe R) : s∈Set.range h.free := by
  have hp:fires R s.val.val=quiet W:= Subtype.ext (not_nonempty_iff_eq_empty.mp fun hx=>s.property (Or.inr hx))
  obtain ⟨t,H⟩:= h.backed hq s.val hp
  exact ⟨(⟨t, fun hs=> s.property (H ▸ (h.beams t).mp hs)⟩:Exe Q),Subtype.ext H⟩

-- compatibility with unmarked supplier
variable (ht : Boosted T P x) (r : Config G c→ℂ)
omit h
lemma rituals {b : Rep G c} {Q : ι→ PaintCan S G x F u b.p.threshold} {R : κ→ PaintCan S G x F u b.p.threshold}
    (h : Film X Q R) (hg : ∀ i,(R i).hues=quiet W → i ∈ Set.range X) (Z : Flux.Vac u b) [Fintype ι] [Fintype κ]
    (hp : Intervals Z r (germ Q ht)) (e : Nonempty (Embedded Z.f (bequeath Q ht))) : Intervals Z r (germ R ht) ∧ Nonempty (Embedded Z.f (bequeath R ht)) := by
  refine ⟨⟨fun i=>(parch R ht i).1,fun D U=> ?_⟩,?_⟩
  · rw [← hp.openVac D U]; apply congr_arg; unfold backgroundU
    let L:=Finset.univ.filter (fun i=> Disjoint (germ Q ht i).extent D)
    let H:=Finset.univ.filter (fun i=> Disjoint (germ R ht i).extent D)
    have hz : L.map h.free=H:= by
      ext i; constructor
      · intro hI; obtain ⟨j,hj,rfl⟩:=mem_map.mp hI; apply mem_filter.mpr; rw [← h.free_bill j ht]
        exact ⟨mem_univ _,(mem_filter.mp hj).2⟩
      intro hi; obtain ⟨v,rfl⟩:= h.renewal hg i
      exact mem_map.mpr ⟨_,mem_filter.mpr ⟨mem_univ _,by rw [h.free_bill v ht]; exact (mem_filter.mp hi).2⟩,rfl⟩
    change Flux.chair _ _ H=Flux.chair _ _ L
    rw [← hz]; symm; apply frames
    exact fun i=> congr_arg Inner.extent (h.free_bill i ht)
    exact fun i=> congr_arg (fun (a:Inner G u)=> (a.glow b.p.threshold).covets U) (h.free_bill i ht)
  obtain ⟨e⟩:=e; refine ⟨⟨e.wire.trans h.differs, fun i=>?_,?_⟩⟩
  · change bequeath R ht (h.differs (e.wire _))=_; rw [← h.movie,e.found]
  intro i hp
  obtain ⟨v,hv⟩:= h.backed hg i.val ((heirs R ht _).1 ▸ hp)
  let p : Inn Q:= ⟨v,(h.beams v).mpr (hv.symm ▸ i.property)⟩
  have he : h.differs p=i:= Subtype.ext hv; obtain ⟨d,hd⟩:=e.film p (by rw [h.movie p ht,he]; exact hp)
  exact ⟨d,(congr_arg _ hd).trans he⟩
end Film
end YM.PhysicalNext.InteractingRank.Display
