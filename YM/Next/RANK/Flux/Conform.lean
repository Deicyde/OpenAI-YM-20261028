import YM.Next.RANK.Flux.Storm
import YM.Next.RANK.Flux.Wraith

/-!
# Monitoring projection by address key
On step side: same vacancy law through attachments, merge order. Compare at
actual footprints; not asserting every reduction can keep this property unless
prior trajectory also used it. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory
open scoped BigOperators Classical

variable {V ι κ α β : Type*} [DecidableEq V] [Fintype V] {G : Gauge} {n : Side} {ζ : V→ Site n} {t : ℝ}
variable (S : ι→ Plug G ζ t) (P : κ → Lining G ζ t)

-- bare path continuation into final sparse assemblies (no log marker requests there)
def Embedded.lining {A : ι→Lifted G ζ t} {F : α→Plug G ζ t} (E : Embedded A F) : Embedded (toRain A P) (panel F P):= ⟨holding P E,equivalence P E,shrunk P E⟩
lemma mainline (i : ι): ({ Sum.inl (β:=κ) i} : Finset _).toLeft={i}:= by ext;simp
lemma asideL (i : ι): ({ Sum.inl (β:=κ) i} : Finset _).toRight=∅:= by ext;simp
def solitary (i : ι) : Party S P:= by
  let Z : Finset (ι⊕κ):={.inl i}
  have ht: Spark (dish S P) Z:=by
    refine ⟨Finset.singleton_nonempty _,fun k hk j hj=> ?_⟩; obtain rfl := mem_singleton.mp hk; obtain rfl := mem_singleton.mp hj; exact .refl
  have he: glasses S P Z:= by
    unfold glasses; rw [show Z.toLeft={i} from mainline i,show Z.toRight=∅ from asideL i]; simp
  exact ⟨Z,ht,he⟩
lemma south (p : Party S P) (h : p.val.toRight=∅):∃ i,p=solitary S P i:= by
  obtain ⟨i,hi⟩:=leaning S P p
  have he := mem_toLeft.mp hi; let A:= p.val
  have hf i : Sum.inr i∉p.val:= fun hh=> (notMem_empty _ (show i∈ (∅:Finset κ) from h ▸ mem_toRight.mpr hh))
  have hx v (hv : chain (dish S P) p.val (.inl i) v): v=.inl i:= by
    induction hv with
    | refl=>rfl
    | @tail b j hh hb Hj =>
      cases j with
      | inr j=> exact False.elim (hf j hb.2.1)
      | inl j=>
        subst b
        rcases eq_or_ne i j with rfl|h
        · rfl
        obtain ⟨H,H',x,h₁,h₂⟩:=hb; rw [dishfest] at h₁ h₂; exact False.elim (disjoint_left.mp (p.property.2.1 hi (mem_toLeft.mpr H') h) h₁ h₂)
  refine ⟨i,Subtype.ext ?_⟩; ext a; change _↔ a∈({ Sum.inl i}:Finset _); rw [mem_singleton]; exact ⟨fun h=> hx a (p.property.1.2 _ he _ h), fun h=> h.symm ▸ he⟩

lemma lift_fields {A B : Lifted G ζ t} (h : A.extent=B.extent) (hx : A.inventory=B.inventory) (hp : A.fires=B.fires)
    (hy : ∀ U,A.amount U=B.amount U): A=B:= by
  have heU : A.value=B.value:= funext fun U=> by
    have ht:=congr_arg (fun a:veil V=>a.part B.fires) (hy U)
    rwa [Lifted.amount,Lifted.amount,hp, Poly.part_send,if_pos rfl,Poly.part_send,if_pos rfl] at ht
  cases A; cases B; congr

lemma solo_things (i : ι) :
    let p:= solitary S P i
    lamps S P p=(S i).extent ∧ vital S P p=(S i).inventory ∧ shining S P p=(S i).fires ∧
      ∀ U, toast S P p U=(S i).tolls U:= by
  intro p; have hf:p.val={Sum.inl i}:=rfl
  refine ⟨?_,?_,?_,fun U=>?_⟩ <;> first
    | (rw [lamps,hf,singleton_biUnion,dishfest])
    | (rw [vital,hf,mainline,singleton_biUnion])
    | (rw [shining,hf,singleton_biUnion]; apply Subtype.ext; exact congr_arg (fun z : modes V=> z.val) (p_coverFire _))
    | (rw [toast,hf,prod_singleton];exact p_coverVal _ _)
lemma solo_raid (S : ι→ Lifted G ζ t) (i) : panel (Plug.raid ∘ S) P (solitary (Plug.raid ∘ S) P i)=.raid (S i):= by
  let Z:= Plug.raid ∘ S
  let L:=solitary Z P i
  obtain ⟨hf,hv,hm,hQ⟩:= solo_things Z P i; let T :=toRain S P L
  have ht : panel Z P L= .raid T:= congr_fun (rainbows P S) L
  change panel Z P L = _; rw [ht];apply congr_arg;refine lift_fields hf hv hm fun U=> ?_
  have hy:=patriot Z P L T.needed U; change T.amount _= _
  by_cases h : tint Z P L U
  · exact hy.trans ((if_pos h).trans (hQ U))
  rw [if_neg h] at hy; refine hy.trans ?_
  have he: (S i).value U=0:= by_contra fun h'=>h (show tint _ _ _ _ from Eq.trans (congr_arg (fun x=> x∩ flags _ U) hf) (((S i).flag U h').trans hv.symm))
  symm; rw [Lifted.amount,he, Poly.send_zero]

lemma Embedded.rainfalls {A : ι→Lifted G ζ t} {F : α→Plug G ζ t} (E : Embedded A F) : Nonempty (Embedded A (Plug.raid ∘ evening F)):= by
  have hp (i) : (F (E.wire i)).landed:= by rw [E.found]; exact (A i).needed
  let f:ι↪Dimmed F:= ⟨fun i=> ⟨E.wire i,hp i⟩,fun i j hh=> E.wire.injective (congr_arg Subtype.val hh)⟩
  refine ⟨⟨f,fun i=> (dim_valid F (f i)).symm.trans (E.found _),fun i hi=>?_⟩⟩
  obtain ⟨j,hj⟩:= E.film i.val (by rw [dim_valid F i]; exact hi); exact ⟨j,Subtype.ext hj⟩
lemma Embedded.exhale {A : ι→Lifted G ζ t} {B : α→Lifted G ζ t} (E : Embedded A (Plug.raid ∘ B)) (h : ∀ i, (raised (P i)).fires.val.Nonempty) : Nonempty (Embedded A (Plug.raid ∘ toRain B P)):= by
  let X:=Plug.raid ∘ B
  let f:ι↪ Party X P:= ⟨fun i=> solitary X P (E.wire i),fun i j he=> E.wire.injective (Sum.inl.inj ((show Sum.inl (E.wire i)= Sum.inl (β:=κ) (E.wire j) from singleton_inj.mp (congr_arg Subtype.val he))))⟩
  rw [← rainbows]; refine ⟨⟨f,fun i=>(solo_raid P B _).trans (E.found i),fun i he=>?_⟩⟩
  have hx:i.val.toRight=∅:= by
    apply Finset.not_nonempty_iff_eq_empty.mp; rintro ⟨j,hj⟩; have ht:=limits P (F:=X) (Sum.inr j) i (mem_toRight.mp hj)
    obtain ⟨v,hv⟩:=h j; rw [he] at ht; exact notMem_empty v (ht hv)
  obtain ⟨j,hj⟩:=south X P i hx; rw [hj,solo_raid P B j] at he; obtain ⟨t,rfl⟩:=E.film j he; exact ⟨_,hj.symm⟩
lemma emb_bg [Fintype ι] [Fintype α] {A : ι→Lifted G ζ t} {B : α→ Lifted G ζ t} (E : Embedded A (Plug.raid ∘ B)) (U : Config G n) (i) : column B i U=column A i U:= by
  unfold column
  rw [← Finset.sum_subset (subset_univ (univ.map E.wire)), Finset.sum_map]; apply sum_congr rfl; intro j _
  rw [show B (E.wire j)=A j from Plug.raid.inj (E.found j)]
  intro j _ h; exact if_neg fun H=> (h (by obtain ⟨j,rfl⟩:= E.film j H.1; exact mem_map.mpr ⟨_,mem_univ _,rfl⟩))

end YM.Next.Rank.Flux
