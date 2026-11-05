import YM.RG08.Door.Hams
/-! # Strict variation prices in reserved widths -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade
open scoped BigOperators Topology Real Classical
variable {I E : Type}{α β : I→Type}{r s D τ d n i e : ℕ}{y σ w v δ b c : I→ℝ} {L : I→ Side}{R : ℝ}{G:Gauge}
section
variable {F H:I→BoardU D R G}
private lemma lip {i:I} (h: Quire.Lit (F i e r) (σ i) (b i))(hp : 1/2≤R)(he:Odd (L i).val) (hh:0≤v i)(hk:v i ≤ (L i).val *σ i) :
    Quire.Lit (cream d (F i) (L i) e r) (v i) ((((L i).val:ℝ)^d)*(Fintype.card (Park G (L i)):ℝ)^r*(Real.exp (4*v i)^r)*b i) := by
  unfold cream reelF; apply Quire.Ink.raise (Quire.Ink.additions (fun j _=> Quire.Ink.scale (rays_lit h hp he j hh hk) _) (fun i=>(ling_pos _ _).le)); rw [sum_const,card_univ,nsmul_eq_mul,Real.norm_of_nonneg (by positivity)]
  apply le_of_eq; field_simp
private lemma cake (h:Tin y δ (fun i=>F i e r) σ)(hp:1/2≤R)(he:∀ i,Odd (L i).val)(hh:0≤v)(h1:v ≤ 1)(hk:∀ i,v i ≤ (L i).val *σ i)(hz : Weighed y (fun i=> ((L i).val:ℝ)))(hv : Audience y) : Tin y δ (fun i=>cream d (F i) (L i) e r) v:= by
  obtain ⟨B,hB,H⟩:= h.serves; have hu: Weighed y (fun i=> Real.exp (4*v i)) := (Weighed.constant y (Real.exp_pos 4|>.le)).mono (fun i=>(Real.exp_pos _).le) (fun i=> Real.exp_monotone (mul_le_of_le_one_right (by norm_num) (h1 i)))
  refine ⟨_,((((hz.powers d).times ((fiscal_lot (G:=G) hz hv).powers r)).times (hu.powers r)).times hB),fun i=> Ink.raise (lip (d:=d) (i:=i) (b:=B*δ) ?_ hp (he i) (hh i) (hk i)) ?_⟩ -- fix i binder
  · exact H i
  exact le_of_eq (by simp only [Pi.mul_apply,mul_assoc])
lemma cake_pair (h:Twill y δ (fun i=>F i e r) (fun i=>H i e r) σ)(hp:1/2≤R)(he:∀ i,Odd (L i).val)(hh:0≤v)(h1:v ≤ 1)(hw:0 ≤ σ)(hk:∀ i,v i ≤ (L i).val *σ i)(hz : Weighed y (fun i=> ((L i).val:ℝ)))(hv : Audience y) : Twill y δ (fun i=>cream d (F i) (L i) e r) (fun i=>cream d (H i) (L i) e r) v := by
  constructor
  · exact cake h.one hp he hh h1 hk hz hv
  · exact cake h.two hp he hh h1 hk hz hv
  rw [show _ - _ = (fun i=>cream d (F i-H i) (L i) e r) from funext fun i=>?_]; · exact cake h.goes hp he hh h1 hk hz hv -- motive
  rw [Pi.sub_apply]; unfold cream reelF; simp_rw [Pi.sub_apply, rays_sub (h.one.solo hw i) (h.two.solo hw i) hp (he _),smul_sub,sum_sub_distrib]
end
section
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [∀ i,Fintype (α i)][∀ i,Fintype (β i)]
variable {F V: ∀ i,Rooted E (α i) r}{P Q : ∀ i, Row (α i) (β i)}
lemma twine (h : Twill y δ F V v) : Twill y δ (fun i=>sew (F i)) (fun i=>sew (V i)) v := by
  have hh {F : ∀ i,Rooted E (α i) r} {δ:I→ℝ} (h:Tin y δ F v) : Tin y δ (fun i=> sew (F i)) v := ⟨_,h.serves.choose_spec.1,fun i=>stitching (h.serves.choose_spec.2 i)⟩
  refine ⟨hh h.one, hh h.two,?_⟩; rw [show _-_=(fun i=>sew (F i-V i)) from funext fun i=>sew_sub.symm]; exact hh h.goes
lemma rhyming (h: Tin y b F v) (hp:0≤v) {η:Fin r→I→ℝ}{Q : Fin r→∀ i,Row (α i) (β i)} (ht:∀ j,SafeRow y (η j) (Q j) v)(hx:∀ j,0 ≤ η j)(he:Weighed y (fun i=> (Fintype.card (β i):ℝ))) : Tin y (fun i=> (∏ j, η j i)*b i) (fun i=> rhyme (F i) (fun j=>Q j i)) v := by
  obtain ⟨B,hB,H⟩:=h.serves; choose A hA Hv using ht
  refine ⟨_,(((he.powers r).times (Weighed.prod univ fun j _=> hA j)).times hB),fun i=> Ink.raise (rhyme_receipt (H i) (hp i) (fun j=> mul_nonneg ((hA j).positive i) (hx j i)) (fun j=> Hv j i)) (le_of_eq ?_)⟩; simp only [Pi.mul_apply,prod_mul_distrib]; ring
lemma tw_both (h: Audience y)(hk:RowBoth y δ Q P v)(hv: ∀ i,0 < v i)(hf:Twill y δ F V v)(hp:0 ≤ δ)(hZ:Weighed y (fun i=> (Fintype.card (β i):ℝ))) : Twill y δ (fun i=>spring (F i) (Q i)) (fun i=>spring (V i) (P i)) v := by
  have h1 : 0 ≤ (1:I→ℝ):= fun _=>zero_le_one; have hg: 0≤ v:=fun i=>(hv i).le
  suffices he:Twill y δ (fun i=> rhyme (F i) (fun _=>Q i)) (fun i=> rhyme (V i) (fun _=> P i)) v from twine he
  constructor
  · apply (show Tin y (fun _=>1) _ v from ?_); simpa only [Pi.one_apply,prod_const_one,mul_one] using rhyming hf.one hg (fun j:Fin r=>hk.fresh) (fun _=>h1) hZ
  · apply (show Tin y (fun _=>1) _ v from ?_); simpa only [Pi.one_apply,prod_const_one,mul_one] using rhyming hf.two hg (fun j:Fin r=>hk.again) (fun _=>h1) hZ
  let T i:= rhyme (V i) (fun _=> Q i)
  let Y i:= rhyme (F i-V i) (fun _=>Q i); have hy : Tin y δ Y v := by simpa only [Y,Pi.sub_apply,Pi.one_apply,prod_const_one,one_mul] using rhyming hf.goes hg (fun j:Fin r=>hk.fresh) (fun _=>h1) hZ
  let M (s : Finset (Fin r))(j: Fin r) := if j∈s then P else Q
  let W (s:Finset (Fin r)) (i:I):= rhyme (V i) (fun j=> M s j i)
  have Wp(s:Finset (Fin r))(j): SafeRow y 1 (M s j) v := by unfold M; split; exact hk.again; exact hk.fresh
  have Wr (s:Finset (Fin r)) : Tin y δ (T-W s) v:= by
    induction s using Finset.induction_on with
    | empty=> simp only [W,T,M, notMem_empty,↓reduceIte,sub_self]; exact Tin.zero
    | insert j s hj ih=>
      let b : Fin r→I→ℝ := fun i=>if i=j then δ else 1
      let U a:= if a=j then Q-P else M s a
      let R i:= rhyme (V i) (fun j=> U j i); have hu i : SafeRow y (b i) (U i) v:= by unfold U b; split; exact hk.moves; exact Wp s i
      have ht:=rhyming hf.two hg hu (fun i=> le_of_eq rfl |>.trans (show _≤b i by unfold b; split; exact hp; exact h1)) hZ
      have he : Tin y δ R v:= ht.raise (fun i=>by change (∏ a,b a i)*1 ≤ _; rw [mul_one,prod_eq_single j]; simp [b]; intro k _ hk; simp [b,hk]; simp)
      have hb i : R i=W s i-W (insert j s) i := by
        unfold R W; let a : Fin r→Row (α i) (β i):=fun k=> M s k i; let B := fun k=> M (insert j s) k i
        rw [show (fun j=> U j i)= update a j (a j-B j) from funext fun k=> by by_cases hp:k=j <;> simp [U,M,hp,B,a,hj]]
        exact rhyme_variation (hf.two.solo hg i) (fun p=> (Wp s p).status hv i) (fun p=> (Wp _ p).status hv i) j (fun k hk=> by simp [M,hk])
      convert ih.plus he h using 1; funext i; rw [Pi.add_apply,hb]; exact (sub_add_sub_cancel ..).symm
  rw [show _-_ = (Y+(T-W univ)) from funext fun i=>?_]; · exact hy.plus (Wr univ) h
  unfold Y W T M; simp only [Pi.add_apply,Pi.sub_apply,mem_univ, ↓reduceIte,rhyme_sub (hf.one.solo hg i) (hf.two.solo hg i) (fun _=>hk.fresh.status hv i),sub_add_sub_cancel]
end
end YM.RG08.Door
