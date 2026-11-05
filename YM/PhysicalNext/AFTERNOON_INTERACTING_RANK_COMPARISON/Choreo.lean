import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Gallery

/-!
# Equivariance and marker moves on the unmarked first system

Always retaining log keys and literal footprints. At ONE step, these
lemmata permit rotations in tree & activation law, and extensions from zero
markers to any given Purchases W, keeping the no-color vacuum stamps on
all fields. Do not require the two kernel replica histories match away from
these projections; wards, layout, sample equalities in usage must give the
actual `Walk`. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Sew
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x τ : ℝ} {L : Lantern G S} {T T' : Tube G S} {O : Orchard S}
    {A : Stores S} {P : Teller G} {W V ι κ ν ρ : Type} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] {u : W → Site c} {v : V→Site c}

lemma migration {X : Type} [DecidableEq X] (b : Equiv.Perm X) (s : Finset ι) (F : ι≃κ) (g : ι→Finset X) (h : κ→ Finset X) (hp : ∀ i,h (F i)=(g i).map b.toEmbedding) : ((s.map F.toEmbedding).biUnion h)=(s.biUnion g).map b.toEmbedding := by
  ext i; rw [mem_biUnion, Finset.mem_map_equiv]; simp_rw [Finset.mem_map_equiv]; rw [mem_biUnion]; constructor
  · rintro ⟨j,hj,hv⟩; obtain ⟨j,rfl⟩:=F.surjective j
    rw [Equiv.symm_apply_apply] at hj; rw [hp] at hv; exact ⟨j,hj,Finset.mem_map_equiv.mp hv⟩
  rintro ⟨j,hj,hv⟩; exact ⟨F j,(F.symm_apply_apply j).symm ▸ hj,(hp j).symm ▸ Finset.mem_map_equiv.mpr hv⟩

lemma mark_pass (E : Equiv.Perm (Site c)) (s : Support c) (t : Support c) (U C : Config G c) (hF : flags τ C=(flags τ U).map E.toEmbedding) :
    (s∩flags τ U=t) ↔ (s.map E.toEmbedding ∩ flags τ C=t.map E.toEmbedding):= by rw [hF,← Finset.map_inter]; exact (Finset.map_injective E.toEmbedding).eq_iff.symm
lemma migration_disjoint {X : Type*} (E : Equiv.Perm X) (A : ι→Finset X) (B : κ→Finset X) (F : ι≃κ) (h : ∀ i,B (F i)=(A i).map E.toEmbedding) (s : Finset ι) :
    (s:Set ι).PairwiseDisjoint A ↔ ((s.map F.toEmbedding):Set κ).PairwiseDisjoint B:= by
  constructor
  · intro hs i hi j hj hh; obtain ⟨i,hi₁,rfl⟩:= Finset.mem_map.mp hi; obtain ⟨j,hj₁,rfl⟩:=Finset.mem_map.mp hj
    change Disjoint (B (F i)) (B (F j)); rw [h,h]; exact (Finset.disjoint_map _).mpr (hs hi₁ hj₁ (fun g=>hh (congr_arg F g)))
  rintro hT i hi j hj he; exact (Finset.disjoint_map _).mp (show Disjoint ((A i).map E.toEmbedding) ((A j).map E.toEmbedding) from by
    rw [← h,← h]; exact hT (Finset.mem_map.mpr ⟨i,hi,rfl⟩) (Finset.mem_map.mpr ⟨j,hj,rfl⟩) (fun h=>he (F.injective h)))
lemma ne_map {X : Type*} {E : Equiv.Perm X} {F : ι≃κ} {A : ι→ Finset X} {B : κ→Finset X} (h : ∀ i,B (F i)=(A i).map E.toEmbedding) j : A (F.symm j)=(B j).map E.symm.toEmbedding:=by
  obtain ⟨j,rfl⟩:=F.surjective j; rw [Equiv.symm_apply_apply,h]; ext i; simp
lemma migrate_connect {E : Equiv.Perm (Site c)} (F : ι≃κ) (s : Finset ι) (A : ι→Support c) (B : κ→Support c) (h : ∀ i,B (F i)=(A i).map E.toEmbedding) :
    Spark A s ↔ Spark B (s.map F.toEmbedding):= by
  constructor
  · exact share' h
  have hp t (hS : Spark B t) (hv : t=s.map F.toEmbedding): Spark A s:= by
    subst t; have hp:= share' (ne_map h) hS; have ht : ((s.map F.toEmbedding).map F.symm.toEmbedding)=s:= Finset.ext (fun _ => by simp)
    rwa [ht] at hp
  exact fun hz => hp _ hz rfl
where
  share' {ι κ c} {A : ι→ Support c} {B : κ→ Support c} {F : Equiv ι κ} {E : Equiv.Perm (Site c)} {X : Finset ι} (h : ∀ i,B (F i)=(A i).map E.toEmbedding) (hX : Spark A X): Spark B (X.map F.toEmbedding):= by
    refine ⟨hX.1.map, fun _ hi _ hj=>?_⟩; obtain ⟨i,hi₁,rfl⟩:= mem_map.mp hi; obtain ⟨j,hj₁,rfl⟩:=mem_map.mp hj
    refine Relation.ReflTransGen.lift F ?_ i j (hX.2 i hi₁ j hj₁)
    intro p q H; obtain ⟨hp,hq,g,hs,hl⟩:=H
    exact ⟨mem_map.mpr ⟨_,hp,rfl⟩,mem_map.mpr ⟨_,hq,rfl⟩,E g,(h p).symm ▸ Finset.mem_map_equiv.mpr ((E.symm_apply_apply g).symm ▸ hs),(h q).symm ▸ Finset.mem_map_equiv.mpr ((E.symm_apply_apply g).symm ▸ hl)⟩
-- Ranks only unmarked obligations, markers transported after proof.
section
variable (Q : ι→ PaintCan S G x O u τ) (R : κ→ PaintCan S G x O v τ)
    (F : ι≃κ) (E : Equiv.Perm (Site c)) (D : Equiv.Perm (Site f))
structure Across : Prop where
  towns i : (R (F i)).X=(Q i).X.map E.toEmbedding
  tipping i : (R (F i)).goal=(Q i).goal.map E.toEmbedding
  marks i : (R (F i)).supplies=(Q i).supplies.map D.toEmbedding
  sheets i : (R (F i)).wants=(Q i).wants.map D.toEmbedding
  packs i : (R (F i)).barricade=(Q i).barricade.map E.toEmbedding
  boxes i : (R (F i)).encumbrance=(Q i).encumbrance.map D.toEmbedding
  shade i : (Q i).hues=quiet W
  shaded i : (R i).hues=quiet V
namespace Across
variable {Q R E F D} (t : Across Q R F E D)
include t in
lemma moveCrew (s : Finset ι) : Spark (zones Q) s∧enlist Q s ↔ Spark (zones R) (F.finsetCongr s) ∧ enlist R (F.finsetCongr s):= by
  unfold Equiv.finsetCongr enlist premise; dsimp only [Equiv.coe_fn_mk]
  rw [migrate_connect F s _ (zones R) t.towns,migration_disjoint E _ (fun i=>(R i).barricade) F t.packs, migration_disjoint D _ (fun i=>(R i).encumbrance) F t.boxes,
    migration D s F (fun i=>(Q i).supplies) (fun i=>(R i).supplies) t.marks,migration D s F (fun i=>(Q i).wants) (fun i=>(R i).wants) t.sheets, (Finset.map_injective D.toEmbedding).eq_iff]; simp only [t.shade,t.shaded]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun _ _ _ _ _ _=>Finset.disjoint_empty_left _,fun _ _ _ _ _ _=>Finset.disjoint_empty_left _⟩)

def crosses (t : Across Q R F E D) : Club Q ≃ Club R:= Equiv.subtypeEquiv F.finsetCongr t.moveCrew
lemma zone_covers (i : Club Q) : zone R (t.crosses i)= (zone Q i).map E.toEmbedding:= migration E i.val F (zones Q) (zones R) t.towns
lemma ticket_covers (i : Club Q) : cardGoal R (t.crosses i).val= (cardGoal Q i.val).map E.toEmbedding:= migration E i.val F (fun i=>(Q i).goal) (fun i=>(R i).goal) t.tipping
lemma rises {ℓ : Type} {T : ℓ→ PaintCan S G x O v τ} (ht : ∀ i,(T i).hues=quiet V) (s : Finset ℓ) : fires T s=quiet V:= by
  unfold fires; simp only [ht]; apply Subtype.ext; ext i; simp [scene,Glyph.quiet, Census.quiet]
lemma workers (i : Club Q) : promotes Q i ↔ promotes R (t.crosses i):= by
  unfold promotes; rw [ticket_covers,rises t.shade,rises t.shaded,Finset.map_nonempty]; simp [Glyph.quiet,Census.quiet]
def inn : Inn Q ≃ Inn R := Equiv.subtypeEquiv t.crosses t.workers
def exe : Exe Q ≃ Exe R := Equiv.subtypeEquiv t.crosses (fun i=> not_congr (t.workers i))
end Across

lemma paidGoals (T : ι→ PaintCan S G x O u τ) (h : ∀ i,(T i).hues=quiet W) (i : Inn T) : (cardGoal T i.val.val).Nonempty:= i.property.resolve_right (fun hp=>not_nonempty_empty (Across.rises h i.val.val▸ hp))
def gruel (T : ι→ PaintCan S G x O u τ) (k : Boosted T' P x) (h : ∀ i,(T i).hues=quiet W) (i : Inn T) : Lifted G u τ:= foundering T k i.val (paidGoals T h i)
lemma held_guests (T : ι→ PaintCan S G x O u τ) (k : Boosted T' P x) (h : ∀ i,(T i).hues=quiet W) (i : Inn T): bequeath T k i=Plug.raid (gruel T k h i):= dif_pos (paidGoals T h i)
end
end YM.PhysicalNext.InteractingRank.Display.Sew
