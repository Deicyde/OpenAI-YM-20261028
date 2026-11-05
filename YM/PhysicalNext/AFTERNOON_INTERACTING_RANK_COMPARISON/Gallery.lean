import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Orders
import YM.Next.RANK.Flux.Tower
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Rendered

/-!
# From this inventory to the first-system call

Pack respects exclusions in unforced vacuum: `bouys`, not an independent
ansatz on dilutes. The shape selected as pole priced elsewhere. Match below
on fixed V masks and normalization read; not inferring survival.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Lattice Wilson Pressure RG Filter MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x τ : ℝ} {F : Orchard S} {T : Tube G S} {A : Stores S}
    {P : Teller G} {k : Streak F} {V : Config G c}
    {W ι : Type} [Fintype W] [DecidableEq W] {u : W → Site c} (Q : ι→ PaintCan S G x F u τ) (ht : Boosted T P x)

def principal (b : Club Q) (h : ¬(cardGoal Q b.val).Nonempty) (hx : (fires Q b.val).val.Nonempty) : SourceAt G u:= ⟨zone Q b, fires Q b.val,hx, knows Q b,letter Q b, lamp_meas (observer Q b) ht _,fun _ _ H=>lamp_eq (observer Q b) ht _ H (fun g=>False.elim (h g)),lamp_turn (observer Q b) ht _⟩
lemma old_valid (b : Club Q) (h : ¬(cardGoal Q b.val).Nonempty) (V : Config G c) : validArea Q b V ↔ Healthy τ (zone Q b) V:=by rw [validArea,Healthy, disjoint_iff_inter_eq_empty]; rw [Finset.not_nonempty_iff_eq_empty.mp h]
lemma principal_check (b : Club Q) (h : ¬(cardGoal Q b.val).Nonempty) (hx : (fires Q b.val).val.Nonempty) (V : Config G c):
    (principal Q ht b h hx).amount τ V=proceeds Q T b V := by
  unfold proceeds principal Value.SourceAt.amount; dsimp only
  split
  · rename_i he; rw [masked_eq _ _ _ _ ((old_valid Q b h V).1 he)]
  rename_i he; rw [masked_ne _ _ _ _ (fun hf=>he ((old_valid Q b h V).2 hf)),Poly.send_zero]

def foundering (b : Club Q) (h : (cardGoal Q b.val).Nonempty) : Lifted G u τ where
  extent:= zone Q b
  inventory:= cardGoal Q b.val
  needed:= h
  records:=goalZone Q b
  fires:= fires Q b.val
  remembers:= knows Q b
  value V:= if validArea Q b V then letter Q (T:=T) b V else 0
  meas:= Measurable.ite (measured Q b) (lamp_meas (observer Q b) ht _) measurable_const
  flag U H:= by split at H; exact (by assumption : validArea Q b U); contradiction
  only U V hp hx:= by
    dsimp only; rw [show letter Q (T:=T) _ _=letter Q (T:=T) b V from lamp_eq (observer Q b) ht _ hp (fun _=> hx)]
    split_ifs with hz hh HH
    · rfl
    · exact False.elim (hh (hx.symm.trans hz))
    · exact False.elim (hz (hx.trans HH))
    rfl
  inv z U:= by have hb:(validArea Q b (gauge z U)) ↔ validArea Q b U:= by unfold validArea; rw [gauge_flags]
               dsimp only; simp only [hb,letter,lamp_turn (observer Q b) ht _ z U]
lemma founders_bill (b : Club Q) (h) (V : Config G c) : (foundering Q ht b h).amount V= proceeds Q T b V := by
  unfold Value.Lifted.amount proceeds foundering
  dsimp only; split <;> first|rfl|exact Poly.send_zero _

def promotes (b : Club Q) := (cardGoal Q b.val).Nonempty ∨ (fires Q b.val).val.Nonempty
abbrev Inn:= {b // promotes Q b}
abbrev Exe := {b // ¬ promotes Q b}

def bequeath (b : Inn Q) : Plug G u τ :=
  if h : (cardGoal Q b.val.val).Nonempty then Plug.raid (foundering Q ht b.val h) else Plug.regular (principal Q ht b.val h (Or.resolve_left b.property h))

lemma heirs (b : Inn Q) : (bequeath Q ht b).fires=fires Q b.val.val ∧ (bequeath Q ht b).extent=zone Q b.val ∧
    (bequeath Q ht b).inventory=cardGoal Q b.val.val ∧ ∀ V,(bequeath Q ht b).tolls V=proceeds Q T b.val V:= by
  unfold bequeath; split
  · rename_i h; exact ⟨rfl,rfl,rfl,founders_bill Q ht _ _⟩
  rename_i h; exact ⟨rfl,rfl,(Finset.not_nonempty_iff_eq_empty.mp h).symm,principal_check Q ht _ _ _⟩
def germ (s : Exe Q) : Inner G u:= ⟨zone Q s.val,has Q s.val,fires Q s.val.val,knows Q s.val,letter Q s.val,lamp_meas (observer Q s.val) ht _,fun _ _ H=>lamp_eq (observer Q s.val) ht _ H (fun hv=>False.elim (s.property (Or.inl hv))),lamp_turn (observer Q s.val) ht _⟩
lemma parch (s : Exe Q): (germ Q ht s).fires=quiet W∧cardGoal Q s.val.val= ∅ ∧ ∀ V, ((germ Q ht s).glow τ).covets V=proceeds Q T s.val V := by
  have hp : ¬(cardGoal Q s.val.val).Nonempty:= fun hv=> s.property (Or.inl hv)
  refine ⟨Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp (show ¬(fires Q s.val.val).val.Nonempty from fun he=>s.property (Or.inr he))),Finset.not_nonempty_iff_eq_empty.mp hp,fun V=>?_⟩
  unfold germ Inner.glow CoverReads.covets proceeds; dsimp only
  split
  · rename_i he; rw [masked_eq _ _ _ _ ((old_valid Q s.val hp V).mp he)]
  rename_i he; rw [masked_ne _ _ _ _ (mt ((old_valid Q s.val hp V).mpr) he),Poly.send_zero]

section partition
variable [Fintype ι]
-- here reading tableau explicitly takes Lantern, because valMeter on THIS F.
variable {Q} {L : Lantern G S} (Q' : Rep G c) (Q : ι→ PaintCan S G x L.park u Q'.p.threshold)

private def opposite : (Inn Q⊕Exe Q) ≃ Club Q:= Equiv.sumCompl (promotes Q)
private def correspondent : Finset (Inn Q) × Finset (Exe Q) ≃ Finset (Club Q):= Finset.sumEquiv.symm.toEquiv |>.trans (opposite Q' Q).finsetCongr
omit [Fintype ι] in
private lemma invented (p : Finset (Inn Q)) (s : Finset (Exe Q)) : correspondent Q' Q (p,s) = p.image Subtype.val∪s.image Subtype.val:= by
  change (p.disjSum s).map _=_; ext i; simp only [Finset.mem_map,mem_union,mem_image]; constructor
  · rintro ⟨j|j,h,rfl⟩; exact Or.inl ⟨j, inl_mem_disjSum.mp h,rfl⟩; exact Or.inr ⟨j,inr_mem_disjSum.mp h,rfl⟩
  rintro (⟨j,h,rfl⟩|⟨j,h,rfl⟩); exact ⟨.inl j, inl_mem_disjSum.mpr h,rfl⟩; exact ⟨.inr j,inr_mem_disjSum.mpr h,rfl⟩
-- use relation from Flux. Cross overlap against holes.
private def quietRoom (p : Finset (Inn Q)) (s : Finset (Exe Q)) :=
    (s : Set _).PairwiseDisjoint (fun i=> (germ Q ht i).extent) ∧ ∀ i∈s, Disjoint (zone Q i.val) (p.biUnion fun i=> (bequeath Q ht i).extent)
omit [Fintype ι] in
lemma matched_flags (V : Config G c) (p : Finset (Inn Q)) (s : Finset (Exe Q)) : solid Q V (correspondent Q' Q (p,s)) ↔ unmark (bequeath Q ht) p (flags Q'.p.threshold V)∧quietRoom ht Q' Q p s := by
  let A:=correspondent Q' Q (p,s); let X i:= (bequeath Q ht i).extent; let Y:=p.biUnion X
  have hz: (cardGoal Q (draw Q A)) = p.biUnion fun i=> (bequeath Q ht i).inventory:= by
    unfold A; rw [drawn_marks,invented Q' Q p s, Finset.union_biUnion]; simp_rw [fun i=> (heirs Q ht i).2.2.1]; ext i; constructor
    · intro hi; rcases mem_union.mp hi with h|h
      · obtain ⟨u,hu,hv⟩:=mem_biUnion.mp h; obtain ⟨u,he,rfl⟩:=mem_image.mp hu; exact mem_biUnion.mpr ⟨_,he,hv⟩
      obtain ⟨u,hu,hv⟩:=mem_biUnion.mp h; obtain ⟨u,he,rfl⟩:=mem_image.mp hu
      rw [(parch Q ht u).2.1] at hv; exact (notMem_empty _ hv).elim
    intro h; obtain ⟨u,hu,h⟩:=mem_biUnion.mp h; exact mem_union_left _ (mem_biUnion.mpr ⟨_,mem_image_of_mem Subtype.val hu,h⟩)
  have hi (i : Inn Q) (h : i∈p):i.val∈A:= by unfold A; rw [invented]; exact mem_union_left _ (mem_image_of_mem Subtype.val h)
  have he (i : Exe Q) (h : i∈s):i.val∈A:= by unfold A; rw [invented]; exact mem_union_right _ (mem_image_of_mem Subtype.val h)
  have hx i:X i=zone Q i.val:= (heirs Q ht i).2.1
  constructor
  · rintro ⟨h,H⟩
    refine ⟨⟨fun i hr j hu hs=>?_,hz.symm.trans H⟩,fun i ha j hb hp=>h (he i ha) (he j hb) (mt Subtype.ext hp),?_⟩
    · change Disjoint (X _) (X _); rw [hx,hx]; exact h (hi i hr) (hi j hu) (mt Subtype.ext hs)
    intro i ha; apply Finset.disjoint_left.mpr; intro x hr hy; obtain ⟨j,hj,hb⟩:=mem_biUnion.mp hy; change x∈ X j at hb
    exact Finset.disjoint_left.mp (h (he i ha) (hi j hj) (fun v=>i.property (v.symm ▸ j.property))) hr (hx j ▸ hb)
  rintro ⟨⟨h,H⟩,hv,hl⟩
  have hc i (ha:i∈s) j (hb:j∈p) : Disjoint (zone Q i.val) (zone Q j.val):= Disjoint.mono_right (fun _ hg=>Finset.mem_biUnion.mpr ⟨j,hb,((heirs Q ht j).2.1)|>.symm ▸ hg⟩) (hl i ha)
  refine ⟨fun i h1 j h2 hf=> ?_, hz.trans H⟩
  rw [invented] at h1 h2
  rcases mem_union.mp h1 with h₁|h₁ <;> rcases mem_union.mp h2 with h₂|h₂ <;> obtain ⟨v,hv0,rfl⟩:=mem_image.mp h₁ <;> obtain ⟨y,hy0,rfl⟩:=mem_image.mp h₂
  · change Disjoint (zone Q _) (zone Q _); rw [← hx v,← hx y]; exact h hv0 hy0 (fun e=>hf (congr_arg _ e))
  · exact (hc y hy0 v hv0).symm
  · exact hc v hv0 y hy0
  exact hv hv0 hy0 (fun e=>hf (congr_arg _ e))

-- Preparation unmarked for THIS family
lemma brigade (V : Config G c) (Λ : Config G c→ℂ): tableau Q T Λ V=bouys (Q:=Q') Λ (germ Q ht) (bequeath Q ht) V := by
  unfold tableau bouys; apply congr_arg; rw [sum_filter, ← Equiv.sum_comp (correspondent Q' Q),Fintype.sum_prod_type]; rw [sum_filter]; apply sum_congr rfl; intro i _
  let B j:=(germ Q ht j).extent
  let Y:= i.biUnion fun j=> (bequeath Q ht j).extent
  let S:=Finset.univ.filter fun j=> Disjoint (B j) Y
  split_ifs with h
  · unfold backgroundU chair; rw [mul_sum,← sum_subset (subset_univ S.powerset)]; swap
    · intro j _ hj; apply if_neg; intro hv; apply hj; refine mem_powerset.mpr fun t ht'=> mem_filter.mpr ⟨mem_univ _,?_⟩
      exact ((matched_flags ht Q' Q V i j).1 hv).2.2 _ ht'
    apply sum_congr rfl; intro j hj; split_ifs with hz hs hs
    · change ∏ i∈(i.disjSum j).map (opposite Q' Q).toEmbedding, _= _
      rw [prod_map, Finset.prod_disjSum]; apply congr_arg₂ HMul.hMul
      · exact prod_congr rfl fun k _=> (heirs Q ht k).2.2.2 V|>.symm
      exact prod_congr rfl fun k _=> ((parch Q ht k).2.2 V).symm
    · exact (hs ((matched_flags ht Q' Q V i j).1 hz).2.1).elim
    · exact (hz ((matched_flags ht Q' Q V i j).2 ⟨h,hs,fun t ht'=> (mem_filter.mp (mem_powerset.mp hj ht')).2⟩)).elim
    rw [mul_zero]
  apply sum_eq_zero; intro j _; exact if_neg (fun he=> h ((matched_flags ht Q' Q V i j).1 he).1)
end partition
end YM.PhysicalNext.InteractingRank.Display
