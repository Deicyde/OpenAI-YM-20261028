import YM.Next.RANK.Flux.Pure


/-!
# Support from pure first-system components. Uses n≤2 AFTER proving
all cluster members lie in one cell. No assumption on copies multiplicity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes Spindle Atlas Cells Station Peak Perch
open scoped BigOperators Classical

variable {V ι κ α β : Type} {G : Gauge} {n : Side} {c : Family G} {i h k N p m a b d e M : ℕ} {s : ℝ}

-- present hull pre radius

def Slice [DecidableEq V] [Fintype V] {ζ : V→Site n} (S : ι → SourceAt G ζ) (X : ι) (a : ℕ) := ∀ y∈(S X).fires.val,(S X).extent ⊆ Spindle.patch a (ζ y)
variable {Q : BudgetPoint} {hk : i≤k} {x : Points m} {hN : k≤N}
local notation "ξ" => readers (C:=c) (b:=s) (p:=p) x hN (hk.trans hN)
variable [Fintype ι] [Fintype κ]
section
variable [DecidableEq ι]
lemma inter (W : ι→SourceAt G ξ) (k' : MergeLog W) (H : ∀ i∈k'.val, Slice W i a)
    (hl : (M:ℕ)=walls (clim c.path.levels i)) (hQ : 3*a≤ d*M) (h : roomTest c.path.levels s k p d b) (hn : m≤2) (hp : middle c.path.levels s k≤ i) (hw : Fit c.path.levels s k x) (ht : Allowed c.path.levels s k) : Routes (d*M) (Bond W k') (b*M):= by
  let v:= k'.val; let y:= (Bond W k').fires.val; let ζ:= ξ; let X:= feet W
  have hz: a≤d*M:=by linarith only [hQ,Nat.zero_le a]
  have he : d*M ≤ b*M:= by
    have hf:=h.radius; exact Nat.mul_le_mul_right _ (by omega)
  have hf (u) (H' : u∈v) (j : ((Ship.yard c s hN p).Cell × Fin m)) (hx : j ∈(W u).fires.val) {k : ((Ship.yard c s hN p).Cell × Fin m)} (ht:k∈(W u).fires.val) : separation (ζ j) (ζ k) ≤ a:= (doors _).mp (H u H' j hx ((W u).remembers k ht))
  have hv (u u':((Ship.yard c s hN p).Cell × Fin m)) (hx : separation (ζ u) (ζ u') ≤ d*M): u.1=u'.1:= by
    by_contra hh
    have hi:= periods (C:=c) x s p (hN:=hN) (h:=hk) ht hw hp u u' hh (3*b*M) (hl.symm ▸ h.apart i hp hk)
    linarith only [hi,hx,he,Nat.zero_le (b*M)]
  have hc i' i (hi : i'∈v) (hj:i∈v) (hb : (X i'∩ X i).Nonempty) (u u':((Ship.yard c s hN p).Cell × Fin m)) (hs:u∈(W i').fires.val) (hs': u'∈ (W i).fires.val): separation (ζ u) (ζ u') ≤ 2*a:= by
    obtain ⟨z,hz⟩:=hb
    have hx: separation (ζ u) z ≤ a:= (doors _).mp (H i' hi u hs (mem_inter.mp hz).1); have hP: separation z (ζ u') ≤ a:= (separation_comm ..).trans_le ((doors _).mp (H i hj u' hs' (mem_inter.mp hz).2))
    linarith only [separation_triangle (ζ u) z (ζ u'),hx,hP]
  have hy : Spark X v:= majesty_spark _ k'.property.1
  have hB i' (hk:i'∈v) (j : ((Ship.yard c s hN p).Cell × Fin m)) (he:j∈(W i').fires.val) {i} (h : chain X v i' i) (hi:i∈v) (o : ((Ship.yard c s hN p).Cell × Fin m)) (hl:o∈(W i).fires.val): j.1=o.1:= by
    induction h generalizing o with
    | refl=> exact hv j o (le_trans (hf _ hk j he hl) hz)
    | @tail l s hb hh IH=>
      obtain ⟨H,h',p,hq,hx⟩:=hh; obtain ⟨u,hu⟩:= (W l).chosen; refine (IH H u hu).trans (hv u o ?_); apply (hc _ _ H h' ⟨p,mem_inter.mpr ⟨hq,hx⟩⟩ u o hu hl).trans; linarith only [hQ,Nat.zero_le a]
  obtain ⟨z,hz⟩:= hy.1; obtain ⟨j,hj⟩:= (W z).chosen
  have hs:i≤k:=hk
  have hm:y.card ≤ 2:= calc
    _ ≤ ({j.1} ×ˢ (@univ (Fin m) _)).card:= by
      apply card_le_card;intro i hi; obtain ⟨v,hv,h⟩:= mem_biUnion.mp hi; exact mem_product.mpr ⟨mem_singleton.mpr (hB z hz j hj (hy.2 _ hz _ hv) hv _ h).symm,mem_univ _⟩
    _ ≤ _:= by rw [card_product,card_singleton, one_mul, card_univ,Fintype.card_fin]; exact hn
  have h₂:v.card≤2:= le_trans (b:=y.card) (by
    choose F hF using fun i=>(W i).chosen
    apply le_trans (b:=(v.image F).card); apply le_of_eq (card_image_of_injOn ?_).symm; intro i hi j hj h; exact Classical.byContradiction fun he=> disjoint_left.mp (k'.property.2 hi hj he) (hF i) (h.symm ▸ hF j)
    apply card_le_card; intro j hj; obtain ⟨i,hi,rfl⟩:=mem_image.mp hj; exact mem_biUnion.mpr ⟨_,hi,hF _⟩) hm
  have hx i j (hi:i∈v) (hp:j∈v): (X i ∩ X j).Nonempty:= by
    have hL :∀ b∈v, i≠j → b=i ∨ b=j:= by
      intro b hb he; by_cases ht:b=i; exact Or.inl ht
      by_cases hx:b=j; exact Or.inr hx
      have H := (card_le_card (show ({b,i,j}:Finset ι) ⊆ v from insert_subset hb (insert_subset hi (singleton_subset_iff.mpr hp)))).trans h₂; rw [card_insert_of_notMem (show b∉ ({i,j}:Finset _) by simp [ht,hx]),card_pair he] at H; norm_num at H
    by_cases h:i=j; subst j; rw [inter_self]; exact size_in _
    have hd z (hp:chain X v i z): z=i∨(X i∩X j).Nonempty:= by
      induction hp with
      | refl=>exact Or.inl rfl
      | @tail l s hb hv IH=>
        cases IH with
        | inr hh=>exact Or.inr hh
        | inl ht=>
          rcases hL _ hv.2.1 h with hh|hh; exact Or.inl hh
          subst s; subst l; obtain ⟨_,_,p,he,hj⟩:=hv; exact Or.inr ⟨p,mem_inter.mpr ⟨he,hj⟩⟩
    exact (hd _ (hy.2 _ hi _ hp)).resolve_left (Ne.symm h)
  refine ⟨fun i hi j hj=>.single ⟨hi,hj,?_⟩,fun j hj i hi=>?_⟩
  · obtain ⟨v,hv,hp⟩:=mem_biUnion.mp hi; obtain ⟨w,hq,hk⟩:=mem_biUnion.mp hj; apply (hc _ _ hv hq (hx _ _ hv hq) _ _ hp hk).trans; omega
  obtain ⟨v,hv,hg⟩:= mem_biUnion.mp hj; obtain ⟨w,hx',hl⟩:=mem_biUnion.mp hi; obtain ⟨q,hq⟩:= (W w).chosen
  have hh:=hc _ _ hv hx' (hx _ _ hv hx') _ _ hg hq
  have he':separation (ζ q) i ≤ a:=(doors _).mp (H w hx' q hq hl)
  exact (doors _).mpr ((separation_triangle ..).trans (le_trans (add_le_add hh he') (by omega)))
end
lemma racks (S : ι → Plug G ξ Q.threshold) (P : κ→ Lining G ξ Q.threshold) (u : ι →Prop) (hS : ∀ i : Bright S,u i.val→ Slice (sunny S) i a)
    (v : MergeLog (sunny (panel S P))) (hy : rawclean S P u v)
    (hl : M=walls (clim c.path.levels i)) (hQ : 3*a≤d*M) (h : roomTest c.path.levels s k p d b) (hn : m≤2) (hp : middle c.path.levels s k≤ i) (hw : Fit c.path.levels s k x) (ht : Allowed c.path.levels s k) : Routes (d*M) (Bond _ v) (b*M):= by
  apply inter (hk:=hk) (sunny (panel S P)) v _ hl hQ h hn hp hw ht
  intro j hj v hv
  obtain ⟨x,hx,rfl⟩:= twins S P u j (hy j hj); obtain ⟨h₁,h₂,-⟩:= ties1 S P x
  rw [h₁] at hv; rw [h₂]; exact hS x hx v hv
end YM.Next.Rank.Flux
