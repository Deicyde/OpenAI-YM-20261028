import YM.MergeProof.West.Throne
import YM.Next.RANK.Flux.Routes



/-!
# Support from pure first-system components. Collect using smaller day radius after proving
all cluster members lie in one cell. No assumption on copies multiplicity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Tapes.West
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes Spindle Atlas Cells Station Peak Perch
open scoped BigOperators Classical

variable {V ι κ α β : Type} {G : Gauge} {n : Side} {c : Family G} {i h k N p m a b d e M : ℕ} {s : ℝ}

-- present hull pre radius

variable {Q : BudgetPoint} {hk : i≤k} {x : Points m} {hN : k≤N}
local notation "ξ" => readers (C:=c) (b:=s) (p:=p) x hN (hk.trans hN)
variable [Fintype ι] [Fintype κ]
section
variable [DecidableEq ι]
lemma interMany (W : ι→SourceAt G ξ) (k' : MergeLog W) (H : ∀ i∈k'.val, Slice W i a)
    (hl : (M:ℕ)=walls (clim c.path.levels i)) (hQ : (3+2*m)*a≤ d*M) (h : roomTest c.path.levels s k p d b) (hp : middle c.path.levels s k≤ i) (hw : Fit c.path.levels s k x) (ht : Allowed c.path.levels s k) : Tapes.West.Carport (d*M) (Bond W k') (b*M):= by
  let v:= k'.val; let y:= (Bond W k').fires.val; let ζ:= ξ; let X:= feet W
  have hz: a≤d*M:=by nlinarith only [hQ,Nat.zero_le a,Nat.zero_le (2*m*a)]
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
      obtain ⟨H,h',p,hq,hx⟩:=hh; obtain ⟨u,hu⟩:= (W l).chosen; refine (IH H u hu).trans (hv u o ?_); apply (hc _ _ H h' ⟨p,mem_inter.mpr ⟨hq,hx⟩⟩ u o hu hl).trans; nlinarith only [hQ,Nat.zero_le a,Nat.zero_le (2*m*a)]
  obtain ⟨z,hz⟩:= hy.1; obtain ⟨j,hj⟩:= (W z).chosen
  have hs:i≤k:=hk
  have hm:y.card ≤ m:= calc
    _ ≤ ({j.1} ×ˢ (@univ (Fin m) _)).card:= by
      apply card_le_card;intro i hi; obtain ⟨v,hv,h⟩:= mem_biUnion.mp hi; exact mem_product.mpr ⟨mem_singleton.mpr (hB z hz j hj (hy.2 _ hz _ hv) hv _ h).symm,mem_univ _⟩
    _ ≤ _:= by simp
  have hz' (p l) (hP:p∈v)(hp:l∈v) (i)(hi:i∈(W p).fires.val)(q)(hq:q∈(W l).fires.val): separation (ζ i) (ζ q) ≤ m*(2*a):=by
      have he := hy.2 p hP l hp
      apply le_trans _ (Nat.mul_le_mul_right (2*a) hm)
      have hx : ReflTransGen (glows ζ y (2*a)) i q:= by
        induction he generalizing q with
        | refl=> exact .single ⟨(show i∈v.biUnion _ from mem_biUnion.mpr ⟨p,hP,hi⟩),mem_biUnion.mpr ⟨p,hP,hq⟩, (hf p hP i hi hq).trans (by omega)⟩
        | @tail l s hK hL IH=>
           obtain ⟨z,hz⟩:= (W l).chosen; obtain ⟨h,h',x,hx,hu⟩:=hL
           exact (IH h z hz).tail ⟨mem_biUnion.mpr ⟨l,h,hz⟩, mem_biUnion.mpr ⟨s,h',hq⟩, hc l s h h' ⟨x,mem_inter.mpr ⟨hx,hu⟩⟩ _ _ hz hq⟩
      exact Tapes.West.trek hx
  refine ⟨fun i hi j hj=> ?_,fun j hj i hi=>?_⟩
  · obtain ⟨v,hv,hp⟩:=mem_biUnion.mp hi; obtain ⟨w,hq,hk⟩:=mem_biUnion.mp hj
    exact (hz' _ _ hv hq _ hp _ hk).trans (by nlinarith only [hQ,Nat.zero_le a,Nat.zero_le (2*m*a)])
  obtain ⟨v,hv,hg⟩:= mem_biUnion.mp hj; obtain ⟨w,hx',hl⟩:=mem_biUnion.mp hi; obtain ⟨q,hq⟩:= (W w).chosen
  have hh:=hz' _ _ hv hx' _ hg _ hq
  have he':separation (ζ q) i ≤ a:=(doors _).mp (H w hx' q hq hl)
  exact (doors _).mpr ((separation_triangle ..).trans ((add_le_add hh he').trans (by nlinarith only [he,hQ,Nat.zero_le a,Nat.zero_le (2*m*a)])))
end
lemma r_acks (S : ι → Plug G ξ Q.threshold) (P : κ→ Lining G ξ Q.threshold) (u : ι →Prop) (hS : ∀ i : Bright S,u i.val→ Slice (sunny S) i a)
    (v : MergeLog (sunny (panel S P))) (hy : rawclean S P u v)
    (hl : M=walls (clim c.path.levels i)) (hQ : (3+2*m)*a≤d*M) (h : roomTest c.path.levels s k p d b) (hp : middle c.path.levels s k≤ i) (hw : Fit c.path.levels s k x) (ht : Allowed c.path.levels s k) : Tapes.West.Carport (d*M) (Bond _ v) (b*M):= by
  apply interMany (hk:=hk) (sunny (panel S P)) v _ hl hQ h hp hw ht
  intro j hj v hv
  obtain ⟨x,hx,rfl⟩:= twins S P u j (hy j hj); obtain ⟨h₁,h₂,-⟩:= ties1 S P x
  rw [h₁] at hv; rw [h₂]; exact hS x hx v hv
end YM.Next.Rank.Flux
