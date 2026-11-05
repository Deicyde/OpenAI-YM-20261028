import YM.OPE.Nesting.PriceDrop

/-! Combining the direct and synthetic expansions. If any logarithmic gap
below a root is actually zero, the desired accuracy has already reduced
to the raw rate and we *don't* need high precision at that switch. In the
other case every positive common lower gain is compared via `Escape` on the
entire direct sum. Empty lower system of edges is treated exactly separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting.Composite
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
variable {L:Type}{l:Filter L}{T:L→ℝ}
variable (h:Services C F S)[l.NeBot](hT:Tendsto T l atTop)

section Parent
variable {n:ℕ}{f:Fin n→Tree}{κ:ℝ}{a:(fork n f).Inner→ℝ}
variable {z:Envelope L (fork n f)}(hg:Regular l T (fork n f) κ a z)(v:(fork n f).Leaf→S.Tag)
       {D:(fork n f).Inner→ℕ}{m:ℕ}(c:R.channels m) {γ:ℝ}
abbrev echoRate :=RateLE l T (stacked U R m c z v D) (forkBill κ a v m)
def echoErr :=RateLE l T (fun t=>(Menu.raw z v).charge R m c (Tree.center z) t - stacked U R m c z v D t) (forkBill κ a v m-γ)

include hg h hT γ
lemma chain (hu:gapBelow (fork n f) a D γ) (hγ:0≤γ)
    (h₁:∀ (j:Fin n) (p :Stage U R (rollCaps D j) (f j)),RateLE l T (nShot U R (f j) (down j z) (childWages j v) (childAge j D) p) (expense U R (a (Sum.inl ())) (childAge j a) (childWages j v) p))
    (he:∀ (j:Fin n) (p :Stage U R (rollCaps D j) (f j)),RateLE l T (fun i=> flash U R (f j) (down j z) (childWages j v) p i - nShot U R (f j) (down j z) (childWages j v) (childAge j D) p i) (expense U R (a (Sum.inl ())) (childAge j a) (childWages j v) p - γ)):
    echoErr (γ:=γ) U R v c (κ:=κ) (a:=a) (z:=z) (l:=l) (T:=T) (D:=D) :=by
      have hd:= Fusion.tariff U R hT h _ κ _ _ v hg
      rcases hγ.eq_or_lt with hγ|hγ
      · subst γ; dsimp [echoErr]; rw [sub_zero]
        exact (hd.2.output m c).sub (price_nested U R hg v c h hT h₁) hT
      have h_age (j)(hi:f j≠bud) := inflate.internal_strict (h:=hg.inside j) hγ (hu j) hi
      obtain ⟨H,big,hHp⟩:=escape U R h hT v hg h_age (forkBill κ a v m - γ) c (rollCaps D)
      have hP:=drop_price U R hg v c h hT big hu
      have hΔ:=delta_nested U R hg v c h hT h₁ (γ:=γ) he
      exact ((hHp.add hP hT).add hΔ hT).congr (Eventually.of_forall fun i=> (by dsimp only; abel))
end Parent

lemma bud_shot {t:Tree}{z:Tree.Envelope L t}{D:t.Inner→ℕ}{p:Stage U R (boundNow t D) t}(v:t.Leaf → S.Tag) {s:L} (he:t=bud): nShot U R t z v D p s=1:=by cases t with
 | bud=>rfl
 | fork=>cases he
lemma bud_unique {t:Tree}{k:ℕ}(h:t=bud): Nonempty (Unique (Stage U R k t)):=by cases h; exact ⟨(inferInstanceAs (Unique Unit))⟩
lemma bud_leaf {t:Tree}(h:t=bud):Nonempty (Unique t.Leaf):=by cases h; exact ⟨inferInstanceAs (Unique Unit)⟩ -- k unused implicit danger, remove

variable (γ:ℝ) (hh:0≤γ)
include h hT hh in
lemma nShot_rate {t:Tree}{z:Tree.Envelope L t}(v:t.Leaf → S.Tag){a:t.Inner→ℝ}{D:t.Inner→ℕ} {κ:ℝ}
    (h_g:gapBelow t a D γ)(hg:Regular l T t κ a z)(p:Stage U R (boundNow t D) t) :
     let k:= expense U R κ a v p; RateLE l T (nShot U R t z v D p) k ∧ RateLE l T (fun i=>flash U R t z v p i-nShot U R t z v D p i) (k-γ):=by
       induction t generalizing κ with
       | bud => dsimp only
                have hw(s:L): flash U R bud z v p s - nShot U R bud z v D p s=0:=by rw [bud_flash U R rfl,bud_shot U R _ rfl,sub_self]
                simp_rw [hw]; refine ⟨RateLE.const (X:=ℂ) 1 (by exact hT) |>.mono ?_, (RateLE.zero (X:=ℂ) l T _)⟩
                change 0 ≤ κ*wages v () - wages v () * κ; rw [mul_comm,sub_self]
       | fork n f ih =>
          let h_i (j:Fin n)(c):= ih j (childWages j v) (gapAll_below (h_g j)) (hg.inside j) c
          constructor
          · exact price_nested U R hg v p.2 h hT (fun j c=>(h_i j c).1)
          exact chain U R h hT hg v p.2 h_g hh (fun j c=>(h_i j c).1) (fun j c=>(h_i j c).2)

include hh h hT

set_option maxHeartbeats 600000 in
lemma echo_sized {n:ℕ}{f:Fin n→Tree}{z:Envelope L (fork n f)}{v:(fork n f).Leaf→S.Tag}
       {D:(fork n f).Inner→ℕ}{a:(fork n f).Inner→ℝ}{κ:ℝ} {m:ℕ}(c:R.channels m) (hu:gapBelow (fork n f) a D γ) (hg:Regular l T (fork n f) κ a z) : echoRate (l:=l) (T:=T) (a:=a) (κ:=κ) (z:=z) (D:=D) U R v c ∧ echoErr (γ:=γ) (l:=l) (T:=T) (a:=a) (κ:=κ) (z:=z) (D:=D) U R v c:=by
     have hv j(p):= nShot_rate U R h hT γ hh (childWages j v) (gapAll_below (hu j)) (hg.inside j) p
     exact ⟨price_nested U R hg v c h hT (fun i u=>(hv i u).1),chain U R h hT hg v c hu hh (fun i u=>(hv i u).1) (fun i u=>(hv i u).2)⟩

omit [l.NeBot] h hT hh
lemma empty_gain {n:ℕ}{f:Fin n→Tree}{z:Envelope L (fork n f)}{v:(fork n f).Leaf→S.Tag}
       (D:(fork n f).Inner→ℕ){m:ℕ}(c:R.channels m) (h:∀ j,f j=bud)(s:L): stacked U R m c z v D s = (Menu.raw z v).charge R m c (Tree.center z) s :=by
      have he(p:Branches U R (rollCaps D)) (j:Fin n): nShot U R (f j) (down j z) (childWages j v) (childAge j D) (p j) s = 1 := bud_shot U R (childWages j v) (h j)
      have ht(p:Branches U R (rollCaps D)):factor U R z v p c s=(Menu.raw z v).charge R m c (Tree.center z) s:=by
          letI(j:Fin n):Unique ((f j).Leaf) := Nonempty.some <| bud_leaf (h j)
          let e:(fork n f).Leaf ≃ Fin n:=Equiv.sigmaUnique _ _
          rw [raw_charge]; symm; refine express_reindex (w:=echoTags U R v p) R e ?_ (?_); · funext j; exact seats_bud (z:=down j.1 z) (h j.1) j.2 s
          funext (j:(fork n f).Leaf); exact (bud_token (t:=f j.1) (v:=childWages j.1 v) U R (h j.1) j.2|>.symm)
      unfold stacked; simp_rw [he,prod_const_one,one_mul,ht]
      letI (k:Fin n):Unique (Stage U R (rollCaps D k) (f k)):=Nonempty.some (bud_unique U R (h k))
      rw [@Fintype.sum_unique _ _ (_:Fintype (Branches U R (rollCaps D)))] -- typeclass mismatch
end YM.OPE.Nesting.Composite
