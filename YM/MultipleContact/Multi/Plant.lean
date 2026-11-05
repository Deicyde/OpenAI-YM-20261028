import YM.Push.RELAY_DIFFERENCE.Placement
/-! Coarse joint inequalities for products of actual cutoff residual cylinders. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Arbor
open Function Filter Set MeasureTheory Lattice Cells Extraction Around Push.RelayDifference Wilson
open scoped Topology BigOperators Classical
set_option maxHeartbeats 640000
variable {G:Gauge}{S:Schedule}{N p:ℕ}{α:Type*}[Fintype α]
local notation "Λ" => S.side N p
lemma shift_literal (F:Config G Λ→ℂ)(b:Bool)(s:Signed) : literal (fun z=>oriented F b s z):=by
  intro x t; funext U
  change hand b (F (pull _ _ U))= hand b (F (pull _ _ (translate t U)))
  rw [← pull_one,pull_pull, one_mul]; congr 3
private lemma copyAt (T:Tiling Λ)(F:Config G Λ→ℂ)(b:Bool)(s:Signed)(w:T.Cell)(o:Site Λ): T.copy w (oriented F ((decide (T.hand w)).xor b) ((T.omega w)⁻¹*s) o) = oriented F b s (T.copyMap w o) := by
      rw [copied,mul_inv_cancel_left]; let a:Bool:=decide (T.hand w); have hb:(a).xor (a.xor b)=b:=by cases a <;> cases b <;> decide
      unfold a at hb;rw [hb]
private lemma movedBudget {β:ℝ}{T:Tiling Λ}{k:ℕ}(hm:k≤N)(ht:Cells.span S hm p ∣ T.side.val)(hs:Seam G Λ β)(A:ℝ)(F:Config G Λ→ℂ)
   (hA:Interior ((center S p hm 0).chamber 0) F ∧ (center S p hm 0).rootTest β F ≤ A)
   {o:Site Λ}(hx:o ∈T.margin 0 (3*Cells.span S hm p)) (s:Signed)(b:Bool)(hd:diag s):
   let f:=oriented F b s o; Interior (T.chamber 0) f ∧ T.rootTest β f≤ A:= by
       exact offset (S:=S) hm T β A ht (shift_literal (S:=S) F b s) hs (center_interior (S:=S) hm _ hd _ _ hA.1) ((center_price (S:=S) hm _ F b s hd hA.1 β).le.trans hA.2) hx
private lemma oriented_planted {β:ℝ}(hs:Seam G Λ β){T:Tiling Λ} (m:α→ℕ)(hm:∀i:α,m i ≤ N)(ht:∀i,Cells.span S (hm i) p ∣ T.side.val)
   (A:α → ℝ)(F:α → Config G Λ →ℂ)
   (hA:∀i,Interior ((center S p (hm i) 0).chamber 0) (F i) ∧ (center S p (hm i) 0).rootTest β (F i) ≤ A i)
   (x:α → Site Λ)(hx:∀i,x i∈T.margin (T.which (x i)) (3*Cells.span S (hm i) p))(hi:Injective (T.which ∘ x)) (s:α→Signed)(b:α→Bool)(hd:∀i,diag (s i)):
   ‖moment β (fun U=> ∏ i:α, oriented (F i) (b i) (s i) (x i) U)‖ ≤ ∏ i:α,A i:=by
    classical
    let w i := (T.which (x i)); choose o ho using fun i=>T.pointed (w i) (x i)
    have hx'(i):o i∈T.margin 0 (3*Cells.span S (hm i) p):= by
       refine (T.reflected_margin (o i) (w i) _).2 ?_
       exact Eq.mp (congrArg (fun y=> y ∈ T.margin (w i) _) (ho i)).symm (hx i)
    let s' i := (T.omega (w i))⁻¹ * (s i); let b' i := (decide (T.hand (w i))).xor (b i)
    have hd' i:diag (s' i):=diag_mul (diag_inv (show diag (T.omega (w i)) from rfl)) (hd i)
    let f (i) := oriented (F i) (b' i) (s' i) (o i)
    have hc' i : T.copy (w i) (f i) = oriented (F i) (b i) (s i) (x i) := by
      exact (copyAt (S:=S) T (F i) (b i) (s i) (w i) (o i)).trans (congrArg (oriented (F i) (b i) (s i)) (ho i))
    have hP i : Interior (T.chamber 0) (f i) ∧ T.rootTest β (f i) ≤ A i := movedBudget (S:=S) (T:=T) (hm i) (ht i) hs _ (F i) (hA i) (hx' i) (s' i) (b' i) (hd' i)
    have he := T.planted hs w hi f (fun i=>(hP i).1)
    simp_rw [hc'] at he
    exact he.trans (Finset.prod_le_prod (fun _ _=> T.root_nonneg ..) fun i _=> (hP i).2)
lemma simultaneous {β:ℝ}(hs:Seam G Λ β){n:ℕ}{T:Tiling Λ}(m:Fin n → ℕ)(hm:∀i,m i ≤ N)(ht:∀i,Cells.span S (hm i) p ∣ T.side.val)
   (A:Fin n→ ℝ)(F:Fin n→ Config G Λ →ℂ)
   (hA:∀i,Interior ((center S p (hm i) 0).chamber 0) (F i) ∧ (center S p (hm i) 0).rootTest β (F i) ≤ A i)
   (x:Fin n → Site Λ)(x':Fin n→Cover)(hx:∀i,x i=(wrap Λ) (x' i)) (hsep:∀i j:Fin n,i≠ j → T.side.val < separation (x i) (x j))
   {K:ℕ}(hK:0<K)(hFit:n*(2*K) < T.side.val)(hK':∀i,3*Cells.span S (hm i) p ≤ K):
   ‖moment β (fun U=> ∏ i, F i (translate (x i) U))‖≤ ∏i:Fin n,A i:=by
   classical
   obtain ⟨o,hoi⟩:= T.fits_together x K hK hFit
   let X:=T.newly o; let w(i):X.Cell:= (X.which (x i))
   have ho'(i):x i∈X.margin (w i) (3*Cells.span S (hm i) p):=YM.Extraction.Lease.fewer X (w i) (hK' i) (hoi i)
   have hi:Injective w:=by
       intro i j h
       apply by_contra; intro ne
       have h':= X.extent (v:=w i) (ho' i).1 (h.symm ▸ (ho' j).1)
       exact (hsep i j ne).not_ge h'
   convert oriented_planted (T:=X) (S:=S) hs m hm ht A F hA x ho' hi (fun _=>1) (fun _=>false) (fun _=>rfl) using 1
   congr! 3 -- maybe rfl pull_one

/-- Common margins for repeated placements modulo a micro tiling. Restrict by physical separation separately. -/
lemma grid_margin {T:Tiling Λ}{n:ℕ}(x:Fin n→ Site Λ){K:ℕ}(hK:0<K)(hFit:n*(2*K)<T.side.val):
   ∃ o:Site Λ,∀ v:Site Λ, (∃i,∀a:Axis,T.hom (v a)=T.hom (x i a)) → v∈ (T.newly o).margin ((T.newly o).which v) K:= by
      obtain ⟨o,ho⟩:=T.fits_together x K hK hFit
      refine ⟨o,fun v h=>?_⟩; obtain ⟨i,hi⟩:=h; let U:=T.newly o
      have hh(a:Axis)(y:Site Λ): U.coordinated (U.which y) y a = (T.hom (y a-o a)).val:=by
            rw [Tiling.residual]; change _ % T.side.val= _
            conv_rhs =>arg 1; arg 2; rw [← ZMod.natCast_zmod_val (y a-o a)]
            rw [map_natCast]; symm; exact ZMod.val_natCast ..
      have he(a:Axis):U.coordinated (U.which v) v a=U.coordinated (U.which (x i)) (x i) a:=by
         rw [hh,hh,map_sub,map_sub,hi a]
      refine ⟨fun a=> (show _ from by change U.kind.Strict U.side.val (U.coordinated (U.which v) v a);rw [he];exact (ho i).1 a), fun a=> by rw [he]; exact (ho i).2 a⟩
lemma grid_margin' {T:Tiling Λ}{α:Type*}[Fintype α](x:α→ Site Λ){K:ℕ}(hK:0<K)(hFit:Fintype.card α*(2*K)<T.side.val):
   ∃ o:Site Λ,∀ v:Site Λ, (∃i,∀a:Axis,T.hom (v a)=T.hom (x i a)) → v∈ (T.newly o).margin ((T.newly o).which v) K:=by
    let e:=Fintype.equivFin α; obtain ⟨o,ho⟩:= grid_margin (T:=T) (fun i=>x (e.symm i)) hK hFit
    refine ⟨o,fun v h=>?_⟩; obtain ⟨i,hi⟩:=h
    exact ho _ ⟨e i,by simpa using hi⟩
private lemma edge_separate {Y:Tiling Λ}{v w:Y.Cell}(h:v≠w): Y.side.val ≤ separation (Y.units.embed v) (Y.units.embed w):=by
    obtain ⟨a,hne⟩:= Function.ne_iff.mp h
    have hn: ((lift (v-w) a).natAbs) ≠ 0:= by
       intro e; have he:= congr_fun (wrap_lift (v-w)) a; change ↑(lift (v-w) a) = v a - w a at he
       rw [Int.natAbs_eq_zero.mp e,Int.cast_zero] at he; exact hne (sub_eq_zero.mp he.symm)
    have he : (Y.units.embed v - Y.units.embed w)=Y.units.embed (v-w):= (Y.units.root.map_sub ..).symm
    apply le_trans ?_ (component_le _ a)
    rw [he,Y.units.lift_embed,Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]
    exact le_mul_of_one_le_right (Nat.zero_le _) (by omega)
private lemma burnt {T Y:Tiling Λ} (hh: T.side.val ∣ Y.side.val)(v:Y.Cell)(a:Axis): T.hom (Y.units.embed v a)=0:=by
    obtain ⟨q,hq⟩:=hh
    change T.hom (↑((Y.side.val:ℤ) * (lift v) a))=0
    rw [hq]; simp
private lemma fill_copy {k:ℕ}(hk:k≤N)(Y:Tiling Λ)(hY: Y = center S p hk 0)(u:α→ Site Λ)(x:Y.Cell×α)(h:Site Λ):
   let actual (t:Y.Cell):Site (S.side k p):=by rw [hY] at t; exact t
   Y.copyMap x.1 h = (Y.omega x.1).act h + Y.units.embed x.1:=by
     subst Y
     intro y
     have He:= copy_home S hk (0:Site Λ) x.1; rw [Tiling.copyMap,affine] at He ⊢; simp only [Signed.act_zero,zero_add] at He
     rw [He];rfl
private lemma disparate {k:ℕ}(hk:k≤N)(T Y:Tiling Λ)(hY:Y = center S p hk 0)
   (x:α→ Site Λ) (hx:∀i,4*pdist (x i:Site Λ)≤Y.side.val) (hs:∀i j:α,i≠j → T.side.val < separation (x i:Site Λ) (x j)) (hTY:2*T.side.val < Y.side.val):
   let y(w:Y.Cell×α):= Y.copyMap w.1 (x w.2)
   ∀i j:Y.Cell×α,i≠j → T.side.val < separation (y i:Site Λ) (y j):=by
       intro y i j ne; by_cases h:i.1=j.1
       · have h': i.2 ≠ j.2:=fun hh=>ne (Prod.ext h hh)
         simp [y, Tiling.copyMap,affine,h]; exact hs _ _ h'
       have h'(t:Y.Cell×α): separation (Y.units.embed t.1) (y t) = pdist (x t.2):=by
           rw [show y t=_ from fill_copy hk Y hY x t _, ← pdist_invariant (Y.omega t.1)]
           simp [separation]
       have ht:=edge_separate h; have hi:=hx i.2;have hj:=hx j.2
       have h1:= separation_triangle (Y.units.embed i.1) (y i) (Y.units.embed j.1)
       have h2:= separation_triangle (y i) (y j) (Y.units.embed j.1)
       rw [h' i] at h1
       rw [separation_comm (y j),h' j] at h2
       omega
lemma micro {k:ℕ}(hk:k≤N){T Y:Tiling Λ}(hY:Y = center S p hk 0){m:ℕ}(hm:m ≤ N)(ht:Cells.span S hm p ∣ T.side.val)(h0:T.side.val ∣ Y.side.val)(hTY:2*T.side.val < Y.side.val)
   (x:α→ Site Λ) (hx:∀i,4*pdist (x i:Site Λ)≤Y.side.val) (hs:∀i j:α,i≠j → T.side.val < separation (x i:Site Λ) (x j)) {β:ℝ}(hb:Seam G Λ β)
   (hFit: Fintype.card (Signed × α) * (2*(3*Cells.span S hm p)) < T.side.val)
   (A:α → ℝ)(F:α → Config G Λ →ℂ)
   (hA:∀i,Interior ((center S p hm 0).chamber 0) (F i) ∧ (center S p hm 0).rootTest β (F i) ≤ A i):
   Y.rootTest β (fun U=> ∏ i:α, F i (translate (x i) U)) ≤ ∏ i:α,A i:=by
    classical
    let x' (b:Signed×α):= b.1.act (x b.2); let y(w:Y.Cell×α):= Y.copyMap w.1 (x w.2)
    have hv:= disparate hk T Y hY x hx hs hTY; change ∀ i j, _→ T.side.val < separation (y i) (y j) at hv
    let K:=3*Cells.span S hm p; obtain ⟨o,ho⟩:=grid_margin' (K:=K) x' (mul_pos (by decide) ((S.toDepth hm p).count.property)) hFit
    let X:=T.newly o
    have hq (u:Y.Cell×α)(a:Axis):T.hom (y u a)=T.hom (x' (Y.omega u.1,u.2) a):= by
       unfold y x'; rw [fill_copy hk Y hY x u,Pi.add_apply,map_add,burnt h0, add_zero]
    let v:=X.which ∘ y
    have hi(t:Y.Cell×α) : y t∈X.margin (v t) K:=ho _ ⟨_, hq t⟩
    have hf:Injective v:=by
       intro i j h; by_contra ne
       have h':= X.extent (v:=v i) (hi i).1 (h.symm ▸ (hi j).1)
       exact (hv i j ne).not_ge h'
    have hU:= oriented_planted (T:=X) hb (fun (_:Y.Cell×α)=>m) (fun _=>hm) (fun _=>ht) (fun k=>A k.2) (fun k=>F k.2) (fun i=>hA i.2) y hi hf (fun i=> Y.omega i.1) (fun i=>decide (Y.hand i.1)) (fun _=>rfl)
    let cfg:= fun U=>∏ i:α,F i (translate (x i) U)
    have he (j:Y.Cell)(U):Y.copy j cfg U= ∏ i:α,oriented (F i) (decide (Y.hand j)) (Y.omega j) (y (j,i)) U:=by
         unfold Tiling.copy; dsimp only [cfg]; let D := pull (Y.omega j) (Y.translateBy j) U
         change (if Y.hand j then star (∏ i:α, F i (translate (x i) D)) else ∏ i,F i (translate (x i) D))=_
         have hf'(t:Site Λ):translate t D = pull (Y.omega j) (Y.copyMap j t) U:=by unfold D; rw [← pull_one,pull_pull,mul_one];rfl
         simp_rw [hf' _]
         by_cases h:Y.hand j <;> simp [Push.RelayDifference.oriented,hand, h,y] <;> rfl
    rw [Fintype.prod_prod_type] at hU -- two occurrences?
    change ‖moment β (fun U=>∏ t: Y.Cell×α, oriented (F t.2) (decide (Y.hand t.1)) (Y.omega t.1) (y t) U)‖ ≤ ∏ (_:Y.Cell), ∏ i, A i at hU
    simp_rw [Fintype.prod_prod_type _,← he,Finset.prod_const,Finset.card_univ] at hU
    apply le_of_pow_le_pow_left₀ Y.cells_positive.ne' (Finset.prod_nonneg (fun i _=> ((center S p hm 0).root_nonneg _ _).trans (hA i).2))
    rw [Tiling.powering]; exact hU
end YM.MultipleContact.Arbor
