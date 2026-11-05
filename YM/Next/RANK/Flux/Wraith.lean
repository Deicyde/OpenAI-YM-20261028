import YM.Next.RANK.Flux.Panels

/-!
# Same blank dictionary

Assess in APIs independently of mark weights and propagation attribution. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory
open scoped BigOperators Classical

variable {V ι κ α β : Type*} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side} {ζ : V→ Site n} {t : ℝ}
variable (S : ι→ Plug G ζ t) (P : κ → Lining G ζ t)


def toRain (s : ι→Lifted G ζ t) (P : κ → Lining G ζ t): (H : Party (Plug.raid ∘ s) P) → Lifted G ζ t:=fun i=>
    Capsules _ _ i (by obtain ⟨j,h⟩:=leaning (Plug.raid ∘ s) P i; obtain ⟨x,hx⟩:=(s j).needed; exact ⟨x,mem_biUnion.mpr ⟨j,h,hx⟩⟩)
lemma rainbows (s : ι→Lifted G ζ t) : panel (Plug.raid ∘ s) P= Plug.raid ∘ toRain s P:= by
  ext i; unfold panel; rw [dif_pos (show (vital (Plug.raid ∘ s) P i).Nonempty from (toRain s P i).needed)]; rfl
structure Embedded (S : ι→ Lifted G ζ t) (F : α → Plug G ζ t) where
  wire : ι ↪ α
  found i : F (wire i)=.raid (S i)
  film i : (F i).fires= quiet V → i∈Set.range wire

-- use all-forced mergings for embedding. Need old S land. No blank proof on W.
section
variable {A : ι→ Lifted G ζ t} {F : α→Plug G ζ t} (E : Embedded A F)

def heldSum : ι ⊕ κ ↪ α ⊕ κ:= Function.Embedding.sumMap E.wire (Function.Embedding.refl κ)
private lemma uplift (L) : speck F P (heldSum E L)=speck (Plug.raid ∘ A) P L:= by
  cases L with
  | inl i=> change CoverReads.ofPlug (F (E.wire i))=_;rw [E.found]; rfl
  | inr i=>rfl

lemma notes (s : Finset (ι⊕κ)) (L : Party (Plug.raid ∘ A) P) (h : L.val=s):
    let Z:=s.map (heldSum E); Spark (dish F P) Z ∧ glasses F P Z:= by
  subst s; let p:=L.val; intro Z
  have hp {i a} (h : bonds (dish (Plug.raid ∘ A) P) p i a) : bonds (dish F P) Z (heldSum E i) (heldSum E a):= by
    obtain ⟨hp,hq,h,ha,hx⟩:=h
    refine ⟨mem_map.mpr ⟨_,hp,rfl⟩,mem_map.mpr ⟨_,hq,rfl⟩,h,?_,?_⟩ <;> unfold dish <;>rw [uplift] <;> assumption
  have he : Spark (dish F P) Z:= by
    refine ⟨map_nonempty.mpr L.property.1.1, fun _ hx _ hy=>?_⟩
    obtain ⟨b,hb,rfl⟩:=mem_map.mp hx; obtain ⟨c,hc,rfl⟩:=mem_map.mp hy
    exact ReflTransGen.lift _ (fun _ _ h=>hp h) _ _ (L.property.1.2 _ hb _ hc)
  have hb:Z.toLeft=p.toLeft.map E.wire:= by ext; simp [Z,p,heldSum]
  have hf:Z.toRight=p.toRight:= by ext; simp [Z,p,heldSum]
  refine ⟨he,⟨fun i hi j hj hh=>?_,fun j hj=> ?_⟩⟩
  · obtain ⟨i,hi1,rfl⟩:=mem_map.mp (show i∈ _ from (show i∈p.toLeft.map E.wire from hb ▸ (show i ∈ Z.toLeft from hi))); obtain ⟨j,hj1,rfl⟩:=mem_map.mp (show j∈p.toLeft.map E.wire from hb ▸ (show j∈Z.toLeft from hj))
    change Disjoint (F _).extent (F _).extent;rw [E.found,E.found]; exact L.property.2.1 hi1 hj1 (fun h=>hh (congr_arg _ h))
  obtain ⟨i,hi,⟨x,hx,hg⟩,hp⟩:=L.property.2.2 j (show j∈p.toRight from hf ▸ hj)
  refine ⟨E.wire i,?_,⟨x,by rw [E.found]; exact hx,hg⟩,fun h=>?_⟩
  · rw [hb]; exact mem_map.mpr ⟨_,hi,rfl⟩
  rw [E.found];exact (A i).needed

def holding : Party (Plug.raid ∘ A) P ↪ Party F P where
  toFun L:= ⟨L.val.map (heldSum E), notes P E _ L rfl⟩
  inj' := fun _ _ he=> Subtype.ext (Finset.map_injective (heldSum E) (congr_arg Subtype.val he))

lemma limits (i) (a : Party F P) (hp : i∈a.val): (speck F P i).fires.val⊆((panel F P a).fires).val:= fun _ hx=>
    ((congr_arg Subtype.val (pan_mark F P a)).symm ▸ (mem_biUnion.mpr ⟨_,hp,hx⟩))
lemma shrunk (a : Party F P) (hs : (panel F P a).fires=quiet V) : a ∈ Set.range (holding P E) := by
  let p:= a.val; let f:ι⊕κ↪α⊕κ:=heldSum E
  let X:= p.preimage f f.injective.injOn
  have h:X.map f=p:=by
    ext i; rw [mem_map]; constructor
    · rintro ⟨v,hv,rfl⟩; exact mem_preimage.mp hv
    intro hi; have hz: i∈Set.range f:= by
      cases i with
      | inr j=>exact ⟨.inr j,rfl⟩
      | inl i=>
        have ht: (F i).fires=quiet V:= by
          apply Subtype.ext
          have hp:(F i).fires.val⊆((panel F P a).fires).val:= by
            have ht:= limits P (.inl i) a hi
            change (CoverReads.ofPlug _).fires.val⊆_ at ht; rwa [p_coverFire] at ht
          rw [hs] at hp; exact subset_empty.mp hp
        obtain ⟨j,hj⟩:= E.film i ht; exact ⟨.inl j,congr_arg _ hj⟩
    obtain ⟨i,rfl⟩:=hz; exact ⟨_,mem_preimage.mpr hi,rfl⟩
  have hx:Spark (dish (Plug.raid ∘ A) P) X:=by
    refine ⟨(map_nonempty (f:=f)).mp ?_,fun i hi j hj=> ?_⟩
    · rw [h]; exact a.property.1.1
    have ht := a.property.1.2 (f i) (mem_preimage.mp hi) (f j) (mem_preimage.mp hj)
    have hl {b} (hb:chain (dish F P) p (f i) b) : ∃ j : ι⊕κ,f j=b∧chain (dish (Plug.raid ∘ A) P) X i j:= by
      induction hb with
      | refl=>exact ⟨_,rfl,.refl⟩
      | @tail b y ht hu ih=>
        obtain ⟨x,rfl,hx⟩:=ih
        obtain ⟨H,D,z,hA,hB⟩:=hu; obtain ⟨t,hQ,rfl⟩:=mem_map.mp (show y∈X.map f from h.symm ▸ D)
        refine ⟨_,rfl,hx.tail ⟨mem_preimage.mpr H,hQ,z,?_,?_⟩⟩
        · unfold f dish at hA; rwa [uplift] at hA
        unfold f dish at hB; rwa [uplift] at hB
    obtain ⟨v,hv,hx⟩:=hl ht; exact f.injective hv ▸ hx
  have hK: glasses (Plug.raid ∘ A) P X:= by
    refine ⟨fun i hi j hj he=> ?_,fun j hj=>?_⟩
    · have hp := a.property.2.1 (mem_toLeft.mpr (show Sum.inl (E.wire i)∈a.val from (show f (Sum.inl i)∈p from mem_preimage.mp (mem_toLeft.mp hi)))) (mem_toLeft.mpr (show Sum.inl (E.wire j)∈a.val from (show f (Sum.inl j)∈p from mem_preimage.mp (mem_toLeft.mp hj)))) (E.wire.injective.ne he)
      change Disjoint (F _).extent (F _).extent at hp;rw [E.found,E.found] at hp;exact hp
    obtain ⟨b,hb,⟨x,H₁,H₂⟩,hc⟩:= a.property.2.2 j (mem_toRight.mpr (show Sum.inr j∈a.val from (show f (Sum.inr j)∈p from mem_preimage.mp (mem_toRight.mp hj))))
    have he:∃ i∈X.toLeft,E.wire i=b:= by
      obtain ⟨i|i,hi,hQ⟩:=mem_map.mp (show Sum.inl b∈X.map f from h.symm ▸ mem_toLeft.mp hb); exact ⟨i,mem_toLeft.mpr hi, Sum.inl.inj hQ⟩; cases hQ
    obtain ⟨i,hi,rfl⟩:=he;rw [E.found] at H₁; exact ⟨i,hi,⟨x,H₁,H₂⟩,fun _=> (A i).needed⟩
  exact ⟨⟨X,hx,hK⟩,Subtype.ext h⟩

lemma equivalence (L:Party (Plug.raid ∘ A) P): panel F P (holding P E L)=.raid (toRain A P L):=by
  let J:= holding P E L;let X:= L.val; let Y:=Plug.raid ∘ A; let M:= heldSum (κ:=κ) E; have hp : J.val=X.map M:=rfl
  have hv x: dish F P (M x)=dish Y P x:=by unfold dish;rw [show M x=heldSum E x from rfl,uplift]
  have hh:lamps F P J=lamps Y P L:= by
    unfold lamps; ext; simp only [mem_biUnion,hp,mem_map]; constructor
    · rintro ⟨v,⟨i,hi,rfl⟩,hh⟩; rw [hv] at hh; exact ⟨i,hi,hh⟩
    rintro ⟨i,hi,h⟩; exact ⟨M i,⟨i,hi,rfl⟩,hv i|>.symm ▸ h⟩
  have ht:vital F P J=vital Y P L:=by
    unfold vital; rw [hp];ext; simp [X,M, heldSum,mem_biUnion,E.found,Y]
  have hl:tint F P J=tint Y P L:=by ext; simp [tint,ht,hh]
  have hE: shining F P J=shining Y P L:=by
    unfold shining; rw [hp]; apply (same_scene ..).2; ext; simp only [mem_biUnion,mem_map]; constructor
    · rintro ⟨v,⟨i,hi,rfl⟩,hx⟩; unfold M at hx; rw [uplift] at hx; exact ⟨i,hi,hx⟩
    rintro ⟨i,hi,h⟩; exact ⟨M i,⟨i,hi,rfl⟩,by rw [show M= _ from (show M=heldSum E from rfl), uplift]; exact h⟩
  have hb U : toast F P J U=toast Y P L U:= by unfold toast; rw [hp,prod_map]; exact prod_congr rfl fun i _=> by unfold M; rw [uplift]
  change panel F P J= _; rw [panel, dif_pos (show (vital F P J).Nonempty from ht.symm ▸ (toRain A P L).needed)]
  apply congr_arg; have hlU:(Capsules F P J (show (vital F P J).Nonempty from ht.symm ▸ (toRain A P L).needed)).value= (toRain A P L).value:= by
    ext U; unfold Capsules toRain; dsimp only; rw [hb, hl,hE]; rfl
  exact fields hh ht hE hlU
where
 fields {A B : Lifted G ζ t} (h : A.extent=B.extent) (he : A.inventory=B.inventory) (ht : A.fires=B.fires) (hp : A.value=B.value) : A=B:=by cases A;cases B;congr
end
end YM.Next.Rank.Flux
