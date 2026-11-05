import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Strand
/-! # Light/Dark Projection and singleton equality -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Weaver
open Lattice Wilson Pressure RG MeasureTheory Function Matrix Finset Next.SectorChange
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid Precision Display
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x τ t : ℝ} {L : Lantern G S} {k : Teller G} {W ι α β κ : Type} [Fintype W] [DecidableEq W] {θ : W→ Site c} {T : Rep G c}

abbrev Piqued (K : ι→Lifted G θ t) := {i // 2 ≤ (K i).fires.val.card}
abbrev Priced (K : ι→SourceAt G θ) := {i // 2 ≤ (K i).fires.val.card}

section convert
variable [Fintype ι] [Fintype κ]
variable {P : BudgetPoint} {H : ι→ SourceAt G θ} {K : κ→ Lifted G θ t}
-- bind any A,K. Canonical sum after
lemma melody (K : ι→ Lifted G θ t) (s : Gel.Setting θ) (U): (Gel.freezeKey K s).value U= ∑ j, if Gel.name (K j)=s then (K j).value U else 0:= by
  rw [← Finset.sum_filter]; exact Eq.symm (Finset.sum_subtype _ (fun i=>by simp) (fun i=>(K i).value U))
lemma melodious {K P : Lifted G θ t} (h : K.extent=P.extent) (hp : K.inventory=P.inventory) (hf : K.fires=P.fires) (ht : ∀ i,K.amount i=P.amount i) : K=P:=by
  have he i: K.value i=P.value i:= by
    let V:=K.fires; have hg:=congr_arg (fun p:veil W=>p.part V) (ht i); unfold Lifted.amount at hg; simp only [Poly.part_send] at hg; rwa [if_pos (show V=K.fires from rfl),if_pos (show V=P.fires from hf)] at hg
  exact enter h hp hf (funext he)
where
  enter {K P : Lifted G θ t} (h : K.extent=P.extent) (hp : K.inventory=P.inventory) (hf : K.fires=P.fires) (ht : K.value=P.value) : K=P:=by cases K; cases P;congr
lemma sonnet {J : ι → Lifted G θ t} {E : ι↪κ} (h : Bridle E (Plug.raid ∘ J) (Plug.raid ∘ K)) (s) (he : (s : Gel.Setting θ).val.2.val.card≤1): Gel.freezeKey J s=Gel.freezeKey K s:= by
  have hX i (hi : (J i).fires.val.card≤1): J i= K (E i) := melodic h i hi
  refine melodious rfl rfl rfl (fun U=>?_); unfold Lifted.amount; rw [melody,melody]; apply congr_arg (Poly.send s.val.2)
  symm
  rw [← sum_subset (subset_univ (univ.map E)),sum_map]
  · refine sum_congr rfl fun i _=> ?_
    have hz : Gel.name (K (E i))=Gel.name (J i):=Subtype.ext ((congr_arg₂ Prod.mk (Subtype.ext (congr_arg₂ Prod.mk (h.same i) (h.bank i))) (h.marks i)).symm)
    rw [hz]; split; swap; exact rfl
    next hg => exact congr_arg (fun p : Lifted G θ t =>p.value U) (hX i (show (J i).fires.val.card≤1 from ((congr_arg (fun s:Gel.Setting θ=>s.val.2.val.card) hg).trans_le he))).symm
  intro i _ hh; split
  next ht=> obtain ⟨x,hx⟩:=h.old i ((congr_arg (fun s:Gel.Setting θ=>s.val.2.val.card) ht).trans_le he); exact False.elim (hh (mem_map.mpr ⟨x,mem_univ _,hx⟩))
  rfl
where
  melodic (h : Bridle E (Plug.raid ∘ J) (Plug.raid ∘ K)) (i) (hi : (J i).fires.val.card≤1) : J i=K (E i):= melodious (h.same i) (h.bank i) (h.marks i) (h.prices i hi)

def basso (H : ι → SourceAt G θ) (t : ℝ) (U : Config G c) := ∑ i, if 2 ≤ (H i).fires.val.card then 0 else (H i).amount t U


lemma pianissimo (J : ι → Lifted G θ t) (K : κ→ Lifted G θ t) (hs : ∀ i,2 ≤ (K i).fires.val.card) (i : Gel.Setting θ) (h : i.val.2.val.card≤ 1): Gel.freezeKey (Sum.elim J K) i= Gel.freezeKey J i := by
  apply Eq.symm (sonnet (E:=Embedding.inl) _ i h); refine ⟨fun _=>rfl,fun _=>rfl,fun _=>rfl,?_,fun _ _ _=>rfl⟩
  rintro (j|j) hi; exact ⟨j,rfl⟩
  have h:= hs j; change (K j).fires.val.card≤1 at hi; omega
lemma opus (J : ι→ Lifted G θ t) (K : κ → Lifted G θ t) (h : ∀ i,(K i).fires.val.card≤1) (hp : ∀ i : Gel.Setting θ,i.val.2.val.card≤ 1 → Gel.freezeKey J i=Gel.freezeKey K i) (U : Config G c) : RAIDage J U = RAIDage (Sum.elim K (fun i : Piqued J=> J i.val)) U:=by
  let P:=Sum.elim K (fun i:Piqued J=> J i.val); unfold RAIDage; rw [Gel.all_keys J, Gel.all_keys P]; congr 1
  have hF i: Gel.freezeKey J i= Gel.freezeKey P i:= by
    by_cases hx : i.val.2.val.card≤1; exact (hp i hx).trans (pianissimo K (fun i:Piqued J=>J i.val) (fun i=> i.property) i hx).symm
    refine melodious rfl rfl rfl fun U=> ?_
    unfold Lifted.amount; rw [melody,melody]; apply congr_arg (Poly.send i.val.2); rw [Fintype.sum_sum_type]; symm
    rw [sum_eq_zero (s:=(univ : Finset κ)), zero_add]; swap
    · intro j _; apply if_neg; intro he; exact hx (show i.val.2.val.card≤1 from he ▸ (h j))
    change (∑ j : Piqued J, if Gel.name (J j.val)=_ then _ else _) = _
    rw [← sum_subset (subset_univ (univ.filter (fun j=>2≤(J j).fires.val.card)))]; swap
    · intro j hj hh; rw [if_neg]; intro he; have hz:=(h); have h2:(J j).fires.val.card≤1:=by by_contra h;exact hh (mem_filter.mpr ⟨hj,by omega⟩)
      exact hx (show i.val.2.val.card≤1 from he ▸ h2)
    exact Eq.symm (sum_subtype _ (show ∀ i, i∈_ ↔ (fun j=>2≤(J j).fires.val.card) i from fun i=>by simp) _)
  rw [funext hF]
lemma dark (J : ι→ SourceAt G θ) (t : ℝ) (U : Config G c) : ∑ i,(J i).amount t U = basso J t U+∑ i:Priced J,(J i.val).amount t U:= by
  let v:=univ.filter fun i=> 2 ≤ (J i).fires.val.card; let V:=univ\v
  have he:basso J t U=∑ j∈V,(J j).amount t U:= by
    unfold basso V v; rw [show univ\ _=univ.filter (fun i=> ¬2 ≤ (J i).fires.val.card) from (by ext; simp),sum_filter]; refine sum_congr rfl fun i _=> ?_; split_ifs <;> try rfl
  rw [he,← show ∑ i ∈ v,(J i).amount t U= _ from sum_subtype v (fun i=>by simp [v]) (fun i=>(J i).amount t U)]
  exact (sum_sdiff (subset_univ v)).symm
end convert
end YM.PhysicalNext.InteractingRank.Weaver
