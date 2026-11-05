import YM.Next.RANK.LedgerGate

/-! # Use connectivity before moving masks -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V ι κ X : Type} [Fintype ι] [Fintype κ]
variable {C : Family G} {i k l j m p q d D a N : ℕ} {r : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points m} {hk : i≤k} {h : middle C.path.levels b k ≤ i}

-- pairwise implies connectivity distances in size 2
private lemma stone [DecidableEq V] (P : V → Site n) (u u' : V) (hp : u≠u') (c : ℕ) (H : Relation.ReflTransGen (glows P {u,u'} c) u u') : separation (P u) (P u')≤ c:= by
  have hx i (h : ReflTransGen (glows P {u,u'} c) u i) : u=i ∨ i=u'∧ separation (P u) (P u')≤c := by
    induction h with
    | refl=> exact Or.inl rfl
    | @tail x y _ h ih=>
      rcases mem_insert.mp h.2.1 with H|H
      · exact Or.inl H.symm
      have hz := mem_singleton.mp H; subst y; refine Or.inr ⟨rfl,?_⟩
      cases ih with
      | inl ht=> subst x; exact h.2.2
      | inr hi=> exact hi.2
  exact ((hx _ H).resolve_left hp).2
lemma fits_pair (hn : m≤ 2) (hi : middle C.path.levels b k ≤ i) (hp : roomTest C.path.levels b k p a q) (hz : Fit C.path.levels b k x) (hx : Allowed C.path.levels b k)
    (H : SourceAt G (readers x hN (C:=C) (b:=b) (p:=p) (hk.trans hN))) (B : ℕ) (hg : B = walls (clim C.path.levels i)) (hr : Routes (a*B) H (q*B)) :
    ∃ L : Lane C k b p a x hk,H.fires=litWord p hN b C L.1 L.2.val ∧ H.extent ⊆ dolmens x b q B hN hk L.1 L.2.val:= by
  let ζ:=readers (C:=C) (b:=b) (p:=p) x hN (hk.trans hN);let T:=H.fires.val; obtain ⟨⟨x',j⟩,hj⟩:= H.chosen
  have he : ∀ z∈T,z.1=x':= by
    intro z hz'
    have hw:=hr.old (x',j) hj z hz'
    have ht S (h:ReflTransGen (glows ζ T (a*B)) (x',j) S):S.1=x' := by
      induction h with
      | refl=> rfl
      | @tail c z hh h IH=>
        rcases h with ⟨he₁,he₂,hA⟩
        by_cases hb:c.1=z.1
        · exact hb.symm.trans IH
        have ht : a*B < separation (ζ c) (ζ z):= periods x b p (h:=hk) hx hz hi c z hb (a*B) (by
          rw [hg]; apply le_trans _ (hp.apart i hi hk); linarith only [Nat.mul_le_mul_right (walls (clim C.path.levels i)) hp.radius, Nat.zero_le (q*walls (clim C.path.levels i)),Nat.zero_le (walls (clim C.path.levels i))])
        exact False.elim (ht.not_ge hA)
    exact ht z hw
  let A:=T.image Prod.snd
  have hL:T= {x'} ×ˢ A:= by
    ext v; constructor
    · intro h; exact mem_product.mpr ⟨mem_singleton.mpr (he v h), mem_image.mpr ⟨v,h,rfl⟩⟩
    intro h; obtain ⟨ha,hb⟩:= mem_product.mp h; obtain ⟨w,hw,hW⟩:= mem_image.mp hb; have hh : w=v:= Prod.ext ((he w hw).trans (mem_singleton.mp ha).symm) hW; exact hh ▸ hw
  let W: flame (Fin m):=⟨scene A, H.chosen.image _⟩
  obtain ⟨u,hu⟩:= (yielding hn).2 W
  have hs (i) (ht : i∈ (tale u).val.val) : (x',i)∈T:=by rw [hL]; rw [hu] at ht; exact mem_product.mpr ⟨mem_singleton_self _,ht⟩
  have hx' : H.fires=litWord p hN b C x' u:= Subtype.ext (show T={x'}×ˢ(tale u).val.val by rw [hu]; exact hL)
  refine ⟨⟨x',u,?_⟩,hx',hr.done _ (hs _ (member_mark u))⟩
  cases u with
  | inl i=> trivial
  | inr i=>
    let a':=i.val.1; let u:=i.val.2
    let b':(Ship.yard C b hN p).Cell × Fin m:=(x', a'); let v: (Ship.yard C b hN p).Cell × Fin m:=(x',u)
    have h₁:b'≠ v:= fun h=> i.property.ne (congr_arg Prod.snd h)
    have hT:T={b',v}:= by rw [hL]; rw [← show (tale (.inr i)).val.val=A from congr_arg (fun i : flame _=> i.val.val) hu]; rw [show (tale (.inr i)).val.val=insert a' {u} from rfl]; ext j; rcases j with ⟨p,x⟩; by_cases h:p=x' <;>simp [b',v,h]
    have hw:ReflTransGen (glows ζ {b',v} (a*B)) b' v:= hT ▸ (show ReflTransGen (glows ζ T (a*B)) b' v from hr.old b' (show b'∈T from hT.symm ▸ (show b'∈{b',v} by simp)) v (show v∈T from hT.symm ▸ (show v∈{b',v} by simp)))
    change separation (core _ _ _ _ hk a') (core _ _ _ _ hk u)≤ _
    refine hg ▸ (show separation _ _ ≤ a*B from ?_)
    exact (together x b p hN hk ((Station.wider ..).trans hi) x' a' u).symm.trans_le (stone ζ b' v h₁ (a*B) hw)

lemma tightP (C : Family G) {h : i ≤ k} (s x) (q c : ℕ) (H : middle C.path.levels s k ≤ i) (ht : roomTest C.path.levels s k p c q) (he : Allowed C.path.levels s k)
    (hp : Fit C.path.levels s k x) (B : ℕ) (hv : B= walls (clim C.path.levels i)) (j u : Lane C k s p c (x : Points m) h) (hN : k≤N)
    {z : Site (C.side i p)} (h1 : z∈dolmens x s q B hN h j.1 j.2.val (C:=C) (p:=p)) (h₂ : z∈dolmens x s q B hN h u.1 u.2.val (C:=C) (p:=p)) : u.1=j.1:= by
  by_contra hh
  let b:= (u.1,headMark u.2.val); let a:=(j.1,headMark j.2.val); let X:= readers (C:=C) (b:=s) (p:=p) x hN (h.trans hN)
  have hu : X =X:=rfl
  have hp := periods (C:=C) x s p (hN:=hN) (h:=h) he hp H b a (show b.1≠a.1 from hh) (3*q*B) (hv.symm ▸ ht.apart i H h)
  change _ < separation (X b) (X a) at hp
  have hf : separation (X b) z ≤ q*B:= doors _ |>.1 h₂
  have he : separation z (X a) ≤ q*B:= (separation_comm ..).trans_le (doors _ |>.1 h1)
  linarith only [hp,hf,he,separation_triangle (X b) z (X a),Nat.zero_le (q*B)]

end YM.Next.Rank.Tapes
