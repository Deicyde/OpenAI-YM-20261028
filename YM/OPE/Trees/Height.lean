import YM.OPE.Trees.Plot
/-!
# Active internal subtree of a given cluster tree
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Finset
open scoped Classical
variable {I:Type}{s:Arboreal I}{a b:Finset I} {i j k:I}

structure Active (s:Arboreal I)(a:Finset I): Prop where
    main : s.root∈a
    included : a ⊆ s.zones
    parent {u:I}: u∈a→ s.parent u∈a
lemma Action (s:Arboreal I) : s.Active s.zones := ⟨s.initial, Finset.Subset.refl _,fun {u} _=>s.inward _⟩
variable (h:s.Active a)
lemma Active.ancestral (h:s.Active a) (hx:s.Anc i j)(hp:j∈a): i ∈a:=by
    obtain ⟨n,rfl⟩:=hx; induction n with
    | zero=> exact hp
    | succ n ih=> rw [iterate_succ_apply']; exact h.parent ih
-- Ports, middle, etc.
variable (s a)
def middle:= a.erase s.root
def redact (i):= a.filter fun j=> ¬ s.Anc i j
variable {s a}
lemma rootAlone (h:s.Active a)(he:s.middle a=∅): a={s.root}:=by
    rw [← insert_erase h.main, ← show s.middle a= a.erase s.root from rfl, he]; rfl
lemma redacting (hp:i∈a) : s.redact a i⊆ a:= filter_subset ..
lemma redacted (h:s.Active a)(hp:i∈ s.middle a) : s.Active (s.redact a i):=by
    refine ⟨mem_filter.mpr ⟨h.main,fun hr=>(mem_erase.mp hp).1 hr.excess⟩,Subset.trans (redacting (mem_erase.mp hp).2) h.included,fun {u} hu=> ?_⟩
    obtain ⟨qu,hq⟩:= mem_filter.mp hu; exact mem_filter.mpr ⟨h.parent qu,fun he=>hq (he.joins (Anc.step ..))⟩
lemma redact_gains (hp:i∈a) : (s.redact a i).card < a.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨redacting hp,fun he=> (mem_filter.mp (show i∈ s.redact a i from he.symm ▸ hp)).2 (Anc.same ..)⟩)

/-- A last internal vertex (closest to the current frontier). -/
def Border (s:Arboreal I)(a:Finset I)(i:I): Prop:=∀ k∈a,s.Anc i k → k=i
lemma terminals (h':(s.middle a).Nonempty): ∃ i∈ s.middle a, s.Border a i:=by
    obtain ⟨u,hu,hv⟩:= (s.middle a).exists_max_image s.depth h'; have hx: u≠s.root:=(mem_erase.mp hu).1
    refine ⟨u,hu,fun k hk he=>?_⟩; by_contra ht; exact not_lt_of_ge (hv k (mem_erase.mpr ⟨fun hh=>hx (Anc.excess (hh ▸ he)),hk⟩)) (he.into ht)
lemma redact_one (h:s.Border a i) : s.redact a i = a.erase i:= by
    ext j; rw [redact,mem_filter,mem_erase]; constructor
    · rintro ⟨hs,he⟩; exact ⟨fun hz=> he (hz ▸ Anc.same ..),hs⟩
    rintro ⟨hi,hp⟩; exact ⟨hp,fun h'=> hi (h j hp h')⟩

variable [Fintype I] (s a)
/-- Current insertion positions. With all vertices open, these are the
original leaves. Empty is allowed. -/
def live := univ.filter fun i=> i∉a ∧ s.parent i∈ a
lemma live_iff (i) : i∈ s.live a ↔ i∉a ∧ s.parent i∈a:=by simp [live]
def leaves := s.live s.zones
lemma leaves_are (i:I): i∈ s.leaves↔ i∉ s.zones:=by rw [leaves,s.live_iff]; simp [s.inward]
def inputs (i:I):=(s.live a).filter fun j=> s.Anc i j
def external (i:I):= s.live a \ s.inputs a i
variable {s a}
lemma live_other (hi:i∈a) (he:j∈ s.live a): j≠ i:= fun hh=> (s.live_iff ..|>.1 he).1 (hh ▸ hi)
lemma only_level (h:s.Active a)(hi:i∈ s.live a)(he:j∈a):¬ s.Anc i j:= fun hv=> (s.live_iff ..|>.1 hi).1 (h.ancestral hv he)
lemma lived (h:s.Active a)(hi:i∈ s.live a)(he:j∈ s.live a)(hu:i≠j):¬ s.Anc i j:= fun hv=> only_level h hi (s.live_iff ..|>.1 he).2 (hv.back hu.symm)
lemma halfSpace (hi:j∈ s.inputs a i): j∈ s.live a:= (mem_filter.mp hi).1
lemma inside (h:s.Active a)(hi:i∈a)(he:j∈ s.inputs a i) : s.Anc i (s.parent j):= (show s.Anc i j from (mem_filter.mp he).2).back (live_other hi (halfSpace he))

lemma exterior_mem : j∈ s.external a i↔ j∈ s.live a ∧ ¬ s.Anc i j:=by
    simp [external,inputs]; tauto
lemma aurora {j b c : I}(hp:j∈s.kids i)(hv:k∈s.kids i)(he:j≠k)(hh:s.Anc j b)(hk:s.Anc k c) : s.Fork i b c:= ⟨j,hp,k,hv,he,hh,hk⟩
lemma fork_rest (h:s.Active a)(hi:i∈s.middle a)(he:j∈s.external a i): ∃ u∈ s.zones, s.Anc u (s.parent i)∧ s.Fork u i j:=by
    obtain ⟨hZ,hv⟩:= exterior_mem.mp he; obtain ⟨u,hu,-,hh⟩:= s.divergence hv (only_level h hZ (mem_erase.mp hi).2) (s.closure i) (s.closure j); exact ⟨u,hu, hh.left.1.back hh.left.2,hh⟩
lemma pruned (h:s.Active a)(hi:i∈ s.middle a) : s.live (s.redact a i) = insert i (s.external a i) := by
    obtain ⟨hv,hf⟩:= mem_erase.mp hi; have hc : ¬ s.Anc i (s.parent i):=fun hb=> not_lt_of_ge hb.depth (s.step i hv)
    ext x; rw [s.live_iff,mem_insert, exterior_mem,s.live_iff]; constructor
    · rintro ⟨hX,hY⟩; obtain ⟨he,hY⟩:= (mem_filter.mp hY); by_cases hh:x=i; · exact Or.inl hh
      have hu : ¬ s.Anc i x:= fun ho=> hY (ho.back hh); exact Or.inr ⟨⟨fun hx=> hX (mem_filter.mpr ⟨hx,hu⟩),he⟩,hu⟩
    rintro (rfl|⟨⟨hz,he⟩,hh⟩)
    · exact ⟨fun hz=> (mem_filter.mp hz).2 (Anc.same ..),mem_filter.mpr ⟨h.parent hf,hc⟩⟩
    exact ⟨fun hx=> hz ((mem_filter.mp hx).1),mem_filter.mpr ⟨he,fun hu=>hh (hu.joins (Anc.step ..))⟩⟩
lemma no_shadow (s: Arboreal I)(i a) : i∉s.external a i:=fun hp=> (exterior_mem.mp hp).2 (Anc.same ..)
lemma divide (s:Arboreal I)(a i): s.inputs a i ∪ s.external a i= s.live a:= Finset.union_sdiff_of_subset (filter_subset ..) -- order
lemma divided (s:Arboreal I)(a i): Disjoint (s.inputs a i) (s.external a i) := Finset.disjoint_sdiff
lemma next_leaves (h:s.Border a i)(he:i∈a):s.inputs a i=s.kids i:=by
    ext j; rw [inputs,mem_filter,s.live_iff,s.related]; constructor
    · rintro ⟨⟨hv,hV⟩,hu⟩; have he' : j≠ i:= fun h'=> hv (h'▸he); have hu' := h _ hV (hu.back he'); exact ⟨fun hz=> by rw [hz,s.direct] at hV; exact hv (hz ▸ hV),hu'⟩
    rintro ⟨hv,hp⟩; have hi : j≠i:= by rw [← hp]; exact s.not_parent j hv
    have he':s.Anc i j:= hp ▸ Anc.step .. ; exact ⟨⟨fun hh=>hi (h j hh he'),hp ▸ he⟩,he'⟩
lemma top_roots (s:Arboreal I)(a):s.inputs a s.root=s.live a:= by ext i; rw [inputs,mem_filter]; simp [s.closure]
end YM.OPE.Arboreal
