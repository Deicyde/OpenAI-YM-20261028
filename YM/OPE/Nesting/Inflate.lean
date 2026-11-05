import YM.OPE.Nesting.Escape

/-! High grade terms in an auxiliary simultaneous truncation have the
single-edge penalty needed for changing each intermediate horizon *back*.
Only estimates, not definitions of `nShot`, use that auxiliary expansion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting.Composite
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) {d m:ℕ}

private abbrev raise (h:d ≤ m)(p:Menu.Cut R d) : Menu.Cut R m :=⟨⟨p.1.val,by omega⟩,p.2⟩
def inflate (h:d ≤ m): (t:Tree) → Stage U R d t→ Stage U R m t
 | bud,()=>()
 | fork n f,k=>raise U R h k

namespace inflate
variable {t:Tree}{v:t.Leaf→S.Tag}
lemma inject (h:d ≤ m):Injective (inflate U R h t) := by
     cases t with
     | bud=>apply injective_of_subsingleton (α:=Unit)
     | fork=>
        rintro ⟨⟨j,hj⟩,c⟩ ⟨⟨i,hi⟩,e⟩ he
        have hh:j=i := congr_arg (fun q:Cut R m=>q.fst.val) he
        subst i
        have hq := Sigma.mk.inj he |>.2
        exact congr_arg (fun k=>⟨⟨j,hj⟩,k⟩:R.channels j→Cut R d) (eq_of_heq hq)
@[simp] lemma tag_eq (h:d ≤ m)(p:Stage U R d t): token U R t v (inflate U R h t p)=token U R t v p:=by cases t with
 | bud=>rfl
 | fork =>rfl
@[simp] lemma flash_eq {L:Type}{z:Envelope L t}(h:d ≤ m)(p:Stage U R d t): flash U R t z v (inflate U R h t p)=flash U R t z v p :=by cases t with
 | bud=>cases p; rfl
 | fork=>rfl

lemma surject (h:d ≤ m) (q:Stage U R m t) (hq:t≠bud → (token U R t v q).1 ≤ d) : ∃ p,inflate U R h t p = q :=by cases t with
 | bud=>exact ⟨(), Subsingleton.elim (α:=Unit) _ q⟩
 | fork n f=>
      refine ⟨(⟨⟨q.1.val,Nat.lt_succ_of_le (hq (fun he=>Tree.noConfusion he))⟩,q.2⟩: Cut R d),rfl⟩ -- q def
lemma internal_strict {L:Type}{l:Filter L}{T:L→ℝ}{z:Envelope L t}{a:t.Inner → ℝ}{κ γ:ℝ} {D:t.Inner→ℕ}
     (h: Regular l T t κ a z)(hg:0<γ)(hu:gapAll t κ a D γ)(hq:t ≠ bud): κ < t.topAge κ a:=by
     cases t with
     | bud=>exact (hq rfl).elim
     | fork=> contrapose! hg; change a (Sum.inl _) ≤ κ at hg; exact hu.1.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hg))

lemma drop_cost {a:t.Inner→ℝ}{D:t.Inner→ℕ}{κ γ:ℝ} 
     (q:Stage U R m t) {L:Type}{l:Filter L}{T:L→ℝ}{z:Envelope L t}(h:Regular l T t κ a z) (h_gap:gapAll t κ a D γ) (h_deep : t≠bud) (hq:boundNow t D < (token U R t v q).1) : γ ≤ (token U R t v q).1 * (t.topAge κ a-κ):=by
      obtain ⟨hN⟩:=show True from trivial
      have he: t.topAge κ a-κ≥0:= sub_nonneg.mpr h.ageLower
      cases t with
      | bud=>exact (h_deep rfl).elim
      | fork n f=> exact h_gap.1.trans (mul_le_mul_of_nonneg_right (show ((D (Sum.inl ()) + 1:ℕ):ℝ) ≤ ((token ..).1:ℝ) from by exact_mod_cast Nat.succ_le_of_lt hq) he)

end inflate
variable {n:ℕ}{f:Fin n→Tree}{D H:Fin n→ℕ}
def advance (h:D ≤ H) (p:Branches U R (f:=f) D):Branches U R (f:=f) H:= fun i=>inflate U R (h i) _ (p i)
lemma advance_injective (h:D ≤ H): Injective (advance U R h (f:=f)):=fun p q he=> funext fun i=> inflate.inject U R (h i) (congr_fun he i)

lemma advance_missed (v:(fork n f).Leaf→S.Tag)(h:D ≤ H){p:Branches U R (f:=f) H} (hq:p∈(Finset.univ : Finset _ ) \ Finset.univ.image (advance U R h (f:=f))) : ∃ i,f i≠bud ∧ D i < degrees (echoTags U R v p) i:=by -- fix g? and rcases syntax
   by_contra! h'
   have hi(i):∃ q:Stage U R (D i) (f i), inflate U R (h i) (f i) q=p i:=inflate.surject U R (h i) (p i) (v:=childWages i v) (h' i)
   choose a ha using hi
   have he:=Finset.mem_image_of_mem (advance U R h) (Finset.mem_univ a)
   exact (Finset.mem_sdiff.mp hq).2 (funext ha ▸ he)
end YM.OPE.Nesting.Composite
