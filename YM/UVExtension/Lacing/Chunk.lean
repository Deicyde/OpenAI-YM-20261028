import YM.UVExtension.Lacing.Loads
import YM.MergeProof.Volumes
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Extra.Histories Extra.Histories.Relay Motion Eyelet
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}
variable (B : SectionData F) (H : History G) (N p : ℕ) (A : Hol G) (W : Worth) (M : Music F H N p)

set_option quotPrecheck false
open Push Local Planned.GuardedAtom PhysicalNext.Repeat Lotus YM.MergeProof

set_option synthInstance.maxHeartbeats 160000
def tracks (H:History G)(N p i:ℕ)(A:Hol G)(w:Coefficient F (H.S.side i p)):= Eye w A (H.rep N p i) (Real.sqrt (H.levels.clock.forcedAllowance i))
def photo (i:ℕ)(w:Extra.Histories.Relay.Solo F H p i):= tracks H N p i A w.sil
-- E charts in Solo cut have direct sum lane as from beside. For recursion.
structure Respected (i:ℕ)(L:Fence (F:=F) H N p i A)(Q:Solo F H p (i+1))(P:Solo F H p i): Prop where
    delta : let v:=RoutesF.rain L (photo H N p A (i+1) Q).2 none
            let b:=(M.tone i).index.symm v.1
            P.a= Q.a+b∧photo H N p A i P= ∑ j:Bool,rooms (H.S.side i p) F A _ (aisleN (code _) j) (twain v (tracks H N p i A ((M.tone i).plays (-b))) j)

variable {c':ℝ}{T:Heading F}
lemma stanzaP (i:ℕ)(U V:Coefficient F (H.S.side i p))(h:Eligible U A (H.rep N p i) (Real.sqrt (H.levels.clock.forcedAllowance i))) (hp:Eligible V A (H.rep N p i) (Real.sqrt (H.levels.clock.forcedAllowance i))): tracks H N p i A (beside U V) =∑ j:Bool, rooms (H.S.side i p) F A _ (aisleN (code _) j) (twain (tracks H N p i A U) (tracks H N p i A V) j):=by
    let R j:=twain U V j
    have hs(j):Eligible (R j) A (H.rep N p i) (Real.sqrt (H.levels.clock.forcedAllowance i)):=by cases j; exact hp; exact h
    choose f hf using fun j=> (hs j).pay
    have he' := (merge_budget (code Bool) R h.vigor hf Summable.of_finite).1
    have he: Eligible (beside U V) A (H.rep N p i) (Real.sqrt (H.levels.clock.forcedAllowance i)):=⟨h.hK, merge_format (code Bool) R (fun i=> (hs i).form), _,he'⟩
    have ht:= (stanza (code Bool) R hf Summable.of_finite hs he Summable.of_finite).tsum_eq
    refine ht.symm.trans ((tsum_fintype _).trans (Finset.sum_congr rfl fun i _=>?_))
    cases i <;> rfl
theorem acclaim (h : Vintage.YM.RG.History.Selected H) {i : ℕ} (hm : i<N)
    (hl : Heard B H N p A i (M.tone i)) (hh : Heard B H N p A (i+1) (M.tone (i+1)))
    (hu : Responds B H N p W i (M.tone (i+1)) (M.tone i)){t η:ℝ}{D:GaugeDoor (H.rep N p (i+1)) (H.rep N p i)}(hv:Carol B H N p i D (M.tone (i+1)) (M.tone i) t) {Q:Solo F H p (i+1)}
    (K:Planned.GuardedAtom.Guard.Keeper (H.rep N p (i+1)).p (H.rep N p (i+1)).activities)
    (V:Set Wing)(hV:V.Finite)(L0:Fence (F:=F) H N p i A)(ht:Manor B H N p i A K D V L0 T c' η t)
    (hx:(1+2*(H.levels.params i).columns)*η ≤ barunit (H.S.block i))(he:0≤η)(hk':Real.sqrt (H.levels.clock.forcedAllowance (i+1))≤1)
    (hy : Keyed H N p A (i+1) Q) : ∃ P,Keyed H N p A i P ∧ Answers B H N p W M i Q P ∧ Respected H N p A M i L0 Q P ∧ Accord B H N p M t i D Q P :=by
  let R := H.rep N p i
  let L := H.S.block i
  have hK:=ht.good; let X:=V; have hX:=hV
  have H' :=burden B H N p i A K Q.sil V D L0 none h hm hy.format hy.cost (show Q.sil.x=_ from hy.key) he ht hk'
  obtain ⟨U,hW,Hk,hδ⟩:=H'.mints
  simp only [show peat t (F:=F) none=(0:ℝ) from rfl, zero_add, hy.key,map_zero] at Hk hW
  simp only [Frame.coeffSize, Pi.zero_apply,norm_zero, Finset.sum_const_zero,mul_zero,zero_add,vowel] at hW Hk -- Warning .lead map target rew.Pi stuff.
  have hD:= hW.agrees; have hP:=hW.bound; have hU:=hW.format
  have hq:= hW.leadP; rw [sub_zero] at hq; have hQ:= le_trans (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (orbitCost_one_le F)) hq
  let l := M.tone i
  let b := l.index.symm U.x
  have hb : (l.plays b).x=U.x := by
    rw [show (l.plays b).x=l.index b from hl.currents _]; exact l.index.apply_symm_apply _
  let c := (H.levels.params i).columns
  have hc : 0 ≤ c := zero_le_one.trans (H.levels.params i).columns_ge
  let e := η*Q.bill
  have hq : 0≤Q.bill := rem_nonneg hy.cost
  have hs : η ≤ barunit L := (le_mul_of_one_le_left he (by linarith : 1≤(1+2*c))).trans hx
  have hN (v : F.Coeff) (hx : F.coeffSize (l.index v) ≤ e) : l.charge v ≤ c*e :=
    (hl.cone v).trans (mul_le_mul_of_nonneg_left ((Work.G08.size_core ..).trans hx) hc)
  have hp : l.charge b ≤ c*e := hN b ((hl.currents b).symm ▸ hb.symm ▸ hQ)
  have hj : l.charge (-b) ≤ c*e := hN _ (by
    rw [map_neg,show l.index b=U.x from l.index.apply_symm_apply U.x]
    simpa [Frame.coeffSize,e] using hQ)
  let P : Solo F H p i := ⟨Q.a+b, beside U (l.plays (-b)), e+l.charge (-b)⟩
  obtain ⟨Hn,Hp⟩ := presentation hU hP (hl.earns (-b)).1 (hl.earns (-b)).2
  have hk : Keyed H N p A i P := by
    refine ⟨Hn,Hp,?_⟩
    change (beside U (l.plays (-b))).x=0; rw [reckon,show (l.plays (-b)).x=_ from hl.currents _,map_neg]
    rw [show (M.tone i).index b=U.x from l.index.apply_symm_apply _]; exact add_neg_cancel _
  refine ⟨P,hk,⟨?_,?_⟩,?_,?_⟩
  · intro v
    let y := Q.a+v
    let j := vowel F L ((M.tone (i+1)).plays y).x
    obtain ⟨hn,hd,J,hJ,hX,hY⟩ := hu.tally y
    have hF := keys B H N p A M v hy hh
    have hG := keys B H N p A M v hk hl
    have hw : P.a+v=y+b := by unfold P y; simp [add_right_comm]
    have hi : (P.bar M v).x=(M.tone i).index y+ U.x := by rw [hG.1,hw,map_add,show (M.tone i).index b=U.x from l.index.apply_symm_apply _]
    have hj' : (Q.bar M v).x=((M.tone (i+1)).plays y).x := by rw [hF.1,hh.currents]
    have hz : ((M.tone i).plays y).x=(M.tone i).index y := hl.currents y
    rw [hj',hi,← hz]
    refine ⟨rem_nonneg hG.2.2,rem_nonneg hF.2.2,J,hJ,?_,?_⟩
    · rw [show ((M.tone i).plays y).x+U.x - J j = (((M.tone i).plays y).x-J j) + U.x by abel]
      refine (Size.add F _ _).trans ((add_le_add hX hQ).trans ?_)
      have hb : η * Q.bill ≤ barunit L * Q.bill := mul_le_mul_of_nonneg_right hs hq
      unfold Solo.cost
      change _ ≤ barunit L * (F.coeffSize (F.core ((M.tone (i+1)).plays y).x)+(Q.bill+(M.tone (i+1)).charge y))
      simp only [mul_add, L] at *; linarith
    unfold Solo.cost
    rw [hw]
    change e+l.charge (-b)+l.charge (y+b) ≤ _
    refine (add_le_add_right (hl.summed y b) _).trans ?_
    have hv : (1+2*c)*η*Q.bill ≤ barunit L*Q.bill := mul_le_mul_of_nonneg_right hx hq
    calc
      _ ≤ e+c*e+(l.charge y+c*e) := add_le_add (add_le_add_right hj _) (add_le_add_right hp _)
      _ = l.charge y+(1+2*c)*η*Q.bill := by unfold e; ring
      _ ≤ _ := (add_le_add hY hv).trans_eq (by unfold L y; ring)
  · intro v
    let f (x) := (l.plays x).density 0 B R
    have hf : IsLinearMap ℂ f := hl.values
    let Fm := H.rep N p (i+1)
    let g (P : Coefficient F (H.S.side (i+1) p)) := P.density 0 B Fm
    let u := Q.a+v
    let K := (M.tone (i+1)).plays u
    have Hw := (h.represents N p (i+1) hm).good
    have HR := (h.represents N p i hm.le).good
    have hc : (P.bar M v).density 0 B R=blast H N p i d (g Q.sil)+ f u := by
      change (beside P.sil _).density _ B R = _
      have hc := plus HR Hp (hl.earns (P.a+v)).2 B
      rw [hc, plus HR hP (hl.earns (-b)).2 B,hD]
      rw [show P.a+v = b+u by unfold P u; simp [add_comm, add_assoc]]
      change _ + f (-b) + f (b+u)=_+f u
      rw [hf.map_add, (show f (-b) = -f b from (IsLinearMap.mk' f hf).map_neg b)]; abel
    have hu : f u= blast H N p i d (g K) := hu.values _
    rw [hc,hu,show (Q.bar M v).density 0 B Fm = g Q.sil + g K from plus Hw hy.cost (hh.earns u).2 B]
    unfold blast
    rw [StepData.push_add (H.levels.transition_mass ..) _ _
      (Vintage.YM.Extra.Histories.play_integrable H N h hm hy.format hy.cost) (Vintage.YM.Extra.Histories.play_integrable H N h hm (hh.earns u).1 (hh.earns u).2), smul_add]
  · constructor -- record delta
    dsimp only; let v:= photo H N p A (i+1) Q; change _+_=_+_ ∧ photo H N p A i P= _
    rw [show RoutesF.rain L0 v.2 none=_ from hδ.symm,sees]
    have he : Eligible U A (H.rep N p i) (Real.sqrt (H.levels.clock.forcedAllowance i)):=⟨ht.coins,hW.format,_,hW.bound⟩
    refine ⟨rfl,stanzaP H N p A _ U (l.plays (-b)) he ?_⟩; exact ⟨ht.coins,(hl.earns _).1,_,(hl.earns _).2⟩
  obtain ⟨J,hJ,hB⟩:=hv; let E:= X∪J; refine ⟨E,hX.union hJ,fun v=> ?_⟩; intro R' S V; let y:=Q.a+v; let Z:=M.tone (i+1); have hΩ:= (Hk.climb (a:=2*Q.bill) (w:=η*Q.bill) (show (X:Wing→Prop)≤ (E:Wing→Prop) from Set.subset_union_left) le_rfl le_rfl) -- type show simplify
  have hω:= hB y; dsimp only at hω
  have hY:= Tale.plus hΩ (hω.climb (Y:=E) (Set.subset_union_right) le_rfl le_rfl) hK
  have heq : V.x= Z.index y:= (keys B H N p A M v hy hh).1
  have hi : profile S.activities (P.bar M v).forced=profile S.activities U.forced+profile S.activities (l.plays y).forced:=by
     let f (x) := profile S.activities (l.plays x).forced; have hf : IsLinearMap ℂ f:= inkL _ _ hl.book (fun i=> (hl.earns i).2)
     have hp' := duo_profile Hp (hl.earns (P.a+v)).2; rw [show profile S.activities (P.bar M v).forced= _ from hp',duo_profile hP (hl.earns (-b)).2,show P.a+v=b+y by unfold P y; simp [add_comm,add_assoc]]
     change _ + f (-b)+f (b+y)=_+f y; rw [hf.map_add,(show f (-b) = -f b from (IsLinearMap.mk' f hf).map_neg _)]; abel
  rw [hi,heq,show V.exponentialEntry 0 B R'= _ from duo_exp B hy.cost (hh.earns y).2,show profile R'.activities V.forced= _ from duo_profile hy.cost (hh.earns y).2]; rw [zero_add] at hY -- will rewrite profiles? just x
  refine hY.climb le_rfl ?_ ?_
  · unfold Relay.weighted; unfold Solo.cost y Z; linarith only [rem_nonneg (hh.earns (Q.a+v)).2]
  change e+l.charge y ≤ e+l.charge (-b)+l.charge (P.a+v)
  rw [add_assoc]; apply add_le_add le_rfl; have heq : (-b)+(P.a+v)=y:=by rw [show P.a+v = b+y by unfold P y; simp [add_comm,add_assoc]]; abel
  exact (congr_arg l.charge heq.symm).trans_le (hl.summed _ _)
end YM.UVExtension.Lacing
