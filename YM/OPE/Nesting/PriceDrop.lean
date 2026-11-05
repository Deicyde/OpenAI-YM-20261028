import YM.OPE.Nesting.Accelerant

/-! Taking away slots of excessive engineering grade, then replacing each
remaining direct coefficient on a child by a finite composition below it. A
direct-child error or **one** excessive slot suffices, hence a single-edge
penalty rather than invalidly claiming a simultaneous product of gains. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting.Composite
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
variable {L:Type}{l:Filter L}{T:L→ℝ}

variable {n:ℕ}{f:Fin n→Tree}{κ:ℝ}{a:(fork n f).Inner→ℝ}
variable {z:Envelope L (fork n f)}(hg:Regular l T (fork n f) κ a z)(v:(fork n f).Leaf→S.Tag)
       {D:(fork n f).Inner→ℕ} {r:Fin n→ℕ}{m:ℕ}(c:R.channels m)

private def growth (r:Fin n→ℕ):Branches U R (f:=f) r → L→ℂ :=fun q s => (∏ i, flash U R (f i) (down i z) (childWages i v) (q i) s)* factor U R z v q c s
private def unkept (D:(fork n f).Inner→ℕ) (hr:rollCaps D ≤ r):Finset (Branches U R (f:=f) r):= univ \ univ.image (advance U R hr)

include D
lemma growth_extend (hr:rollCaps D ≤ r)(q : Branches U R (rollCaps D)) (s:L): growth U R v c (z:=z) r (advance U R hr q) s= growth U R v c (z:=z) (rollCaps D) q s:=by
     have h(j):flash U R (f j) (down j z) (childWages j v) (advance U R hr q j) = flash U R (f j) (down j z) (childWages j v) (q j) :=by unfold advance; apply inflate.flash_eq
     unfold growth; simp_rw [h]; apply congr_arg (_*·); unfold factor
     apply congr_arg (fun x=> express _ _ _ _ x _); funext j
     exact (inflate.tag_eq U R (v:=childWages j v) (hr j) (q j))

lemma estimate_suffix (hr:rollCaps D ≤ r)(s:L): hinge U R z v r c s - hinge U R z v (rollCaps D) c s = ∑ p∈unkept U R D hr, growth U R v c (z:=z) r p s:=by
     have he:=(sum_sdiff (s₁:=univ.image (advance U R (f:=f) hr)) (s₂:=Finset.univ) (f:=fun p=> growth U R v c (z:=z) r p s) (subset_univ _))
     rw [Finset.sum_image (advance_injective U R hr|>.injOn)] at he; simp_rw [growth_extend U R v c hr] at he
     exact ((eq_sub_iff_add_eq).mpr he).symm
variable {γ:ℝ}[l.NeBot](h:Services C F S)(hT:Tendsto T l atTop)
include hg h hT
lemma drop_price (hr:rollCaps D ≤ r)(h':gapBelow (fork n f) a D γ): RateLE l T (fun s=>hinge U R z v r c s - hinge U R z v (rollCaps D) c s) (forkBill κ a v m - γ):=by
        refine (RateLE.sum (S:=unkept U R D hr) (f:=growth U R v c (z:=z) r) hT ?_).congr (Eventually.of_forall fun s=>(estimate_suffix U R v c hr s).symm)
        exact fun j hj=> (one_term U R hg v h hT c j).mono (sub_le_sub_left (fare_omitted U R hg v D r j hr h' hj) _)

omit [l.NeBot] h D hg in
lemma prod_drop {J:Type} (Z:Finset J)(x y:J→L→ℂ)(a:J→ℝ)(hx:∀j∈Z, RateLE l T (x j) (a j))(hy:∀j∈Z, RateLE l T (y j) (a j)) (he:∀ j∈Z,RateLE l T (fun i=> x j i - y j i) (a j-γ)) : RateLE l T (fun i=> (∏ j∈Z, x j i)-(∏ j∈Z,y j i)) ((∑ j∈Z,a j)-γ):=by
    induction Z using Finset.induction with
    | empty=>simp; exact RateLE.zero l T _
    | @insert j t hj h=>
       let X i:= (∏ j∈t,x j i); let Y i:=(∏ j∈t,y j i); let d:= ∑ i∈t,a i
       let hxy:= h (fun i hi=>hx i (mem_insert_of_mem hi)) (fun i hi=>hy i (mem_insert_of_mem hi)) (fun i hi=>he i (mem_insert_of_mem hi))
       let hX:=RateLE.prod (S:=t) hT (fun i hi=>hx i (mem_insert_of_mem hi))
       simpa only [sum_insert hj,prod_insert hj] using ((((he _ (mem_insert_self _ _)).mul hX).mono (b:=a j+d - γ) (by dsimp only [d]; apply le_of_eq; ring)).add (((hy _ (mem_insert_self _ _)).mul hxy).mono (b:=a j + d - γ) (by dsimp only [d]; apply le_of_eq; ring)) hT|>.congr (Eventually.of_forall (fun i=> (show (x j i-y j i)*X i + (y j i)* (X i - Y i) =x j i*X i-y j i*Y i by ring))))

lemma price_nested (hh:∀ (j:Fin n) (p :Stage U R (boundNow (f j) (childAge j D)) (f j)),RateLE l T (nShot U R (f j) (down j z) (childWages j v) (childAge j D) p) (expense U R (a (Sum.inl ())) (childAge j a) (childWages j v) p)): RateLE l T (stacked U R m c z v D) (forkBill κ a v m):=by
    refine RateLE.sum (S:=Finset.univ) (a:=forkBill κ a v m) hT (fun p (_:p∈(Finset.univ:Finset (Branches U R (rollCaps D))))=>?_)
    have hp:= (RateLE.prod (S:=Finset.univ) hT (fun i _=>hh i (p i))).mul (factor_cost U R hg v h hT c p)
    exact hp.mono (sum_fares_le U R hg v p m)

lemma delta_nested (h_y:∀ (j:Fin n) (p :Stage U R (boundNow (f j) (childAge j D)) (f j)),RateLE l T (nShot U R (f j) (down j z) (childWages j v) (childAge j D) p) (expense U R (a (Sum.inl ())) (childAge j a) (childWages j v) p))
       (he:∀ (j:Fin n) (p :Stage U R (boundNow (f j) (childAge j D)) (f j)),RateLE l T (fun i=> flash U R (f j) (down j z) (childWages j v) p i - nShot U R (f j) (down j z) (childWages j v) (childAge j D) p i) (expense U R (a (Sum.inl ())) (childAge j a) (childWages j v) p - γ)):
       RateLE l T (fun s=>hinge U R z v (rollCaps D) c s-stacked U R m c z v D s) (forkBill κ a v m-γ) := by
          let z₁(j):= flash U R (f j) (down j z) (childWages j v) (n:=boundNow (f j) (childAge j D)); let z₂(j):= nShot U R (f j) (down j z) (childWages j v) (childAge j D)
          let F(p:Branches U R (rollCaps D)) s := ((∏ i:Fin n,z₁ i (p i) s)-(∏ i:Fin n,z₂ i (p i) s)) * factor U R z v p c s
          let χ:=forkBill κ a v m-γ
          refine RateLE.congr (F:=fun i=>∑ p,F p i) (RateLE.sum (f:=F) (a:=χ) hT ?_) (Eventually.of_forall (fun i=> by unfold hinge stacked F; simp_rw [sub_mul,sum_sub_distrib]; rfl))
          intro p hp
          have hf:= prod_drop (γ:=γ) hT Finset.univ (fun i=>z₁ i (p i)) (fun i=>z₂ i (p i)) (fun i=>expense U R (a (Sum.inl ())) (childAge i a) (childWages i v) (p i)) (fun i _=> flash_rate U R (childWages i v) (hg.inside i) h hT (p i)) (fun i _=>h_y i (p i)) (fun j _=>he j (p j))
          refine (hf.mul (factor_cost U R hg v h hT c p)).mono ?_
          have h:=sum_fares_le U R hg v p m; unfold χ; unfold childExpense at h; linarith only [h]
end YM.OPE.Nesting.Composite
