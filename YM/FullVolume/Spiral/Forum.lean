import YM.FullVolume.Rank.Esteem
import YM.FullVolume.Luna.Terms
import YM.FullVolume.Panel.Spokes
/- Rotor estimates with exact tapes. Frames. D.Price chosen on any Chart.Y Keeper qualifying.F -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Tower
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{Y:Hol G}{ι:Type}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna
variable {i:ℕ}{F:Labels.Frame G i}{B:BudgetPoint}{q t v a b s:ℝ}{p:sun→ Coefficient F n}{P:Desk G n}{y:F.Coeff}
set_option maxHeartbeats 390000
local notation "A_"=> P.orient
abbrev Stays (p:sun→ Coefficient F n) := ∀ i,(p i).support=(p tip).support
def weave (w:Rung)(p:sun→ Coefficient F n) : Coefficient F n:= ⟨Jams.mix w (fun i=> (p i).x),(p tip).support,Jams.mix w (fun i=>(p i).regular),Jams.mix w (fun i=>(p i).forced)⟩
structure Forum (p:sun→ Coefficient F n)(q:ℝ)(y:F.Coeff)(Y:Hol G)(P:Desk G n)(a b:ℝ): Prop where
   stuck : Stays p
   knows : 1≤q
   burns : ∀ w u,Stripe w q u → F.coeffSize (Jams.mix w (fun i=>(p i).x-y)) ≤ u*a
   earns : ∀ w u,Stripe w q u→ (weave w p).Format 0 Y P.orient ∧ (weave w p).remBound 0 P.orient P.k (u*b)
namespace Forum
variable (h:Forum p q y Y P a b)
include h
lemma enlarge (ha: a ≤ t)(hb:b ≤v):Forum p q y Y P t v:=⟨h.stuck,h.knows,fun w u ht=> (h.burns w u ht).trans (mul_le_mul_of_nonneg_left ha (stripe_pos ht)),fun w u ht=>⟨(h.earns w u ht).1,rem_mono (h.earns w u ht|>.2) (mul_le_mul_of_nonneg_left hb (stripe_pos ht))⟩⟩
lemma play (v:sun): F.coeffSize ((p v).x-y) ≤ a ∧ (p v).Format 0 Y P.orient ∧ (p v).remBound 0 P.orient P.k b:=by
   let w:Rung:= Finsupp.single v 1; have hx :Stripe w q 1:= leaf_stripes v h.knows
   have hp{R:Type}[AddCommMonoid R][Module ℝ R](f:sun→ R): Jams.mix w f=f v:= by simp [Jams.mix,w]
   obtain ⟨hr,hq⟩:=h.earns _ _ hx
   rw [show weave w p=p v from (by unfold weave; rw [hp,hp,hp,← h.stuck]),one_mul] at hq -- hr duplicate
   rw [show weave w p=p v from (by unfold weave; rw [hp,hp,hp,← h.stuck])] at hr
   have h':=h.burns _ _ hx; rw [hp,one_mul] at h'; exact ⟨h',hr,hq⟩
omit h
section algebra
lemma mix_apply' {R R':Type}[AddCommMonoid R'][Module ℝ R'](w:Rung) (x:sun→ R→R') (a:R) : Jams.mix w x a=Jams.mix w (fun i=> x i a):=by unfold Jams.mix; rw [Finset.sum_apply];rfl
lemma twisted (w:Rung)(a:ℂ): weave w (fun i=> Extra.Histories.stretch a (p i))= Extra.Histories.stretch a (weave w p):=by
   have hp {X:Type}[AddCommMonoid X][Module ℂ X][Module ℝ X][SMulCommClass ℝ ℂ X](x:sun→X): Jams.mix w (fun i=> a • x i)= a • Jams.mix w x:=by unfold Jams.mix; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> smul_comm ..
   unfold weave Extra.Histories.stretch; dsimp only; rw [hp,hp,hp]
lemma moveWeave (w:Rung)(m:Motion)(x:P.orient.activities.Moves m.1 0)(h:Stays p): audition x (weave w p)= weave w (fun i=> audition x (p i)):=by
   let q:=fun i=> reorient x (p i); have he: reorient x (weave w p)=weave w q:=by
       unfold q weave reorient; dsimp only; congr 1
       · have hm:= F.act m.1.ortho; unfold Jams.mix; simp_rw [aspect, map_sum,map_smul]
       · funext i V; rw [mix_apply',mix_apply',Function.comp_apply,mix_apply',mix_apply'];rfl
       · funext i V; rw [mix_apply',mix_apply',Function.comp_apply,mix_apply',mix_apply'];rfl
   unfold audition; cases m.2
   · exact he
   · change barAll _=_; rw [he]; change barAll (weave w q)= weave w (fun i=>barAll (q i)); unfold barAll weave; dsimp only; congr 1
     · unfold Jams.mix; simp_rw [star_sum,star_smul,star_trivial]
     · funext i V; rw [mix_apply',mix_apply']; simp only [Pi.star_apply,mix_apply']; unfold Jams.mix; simp_rw [star_sum,star_smul,star_trivial]
     funext i V; rw [mix_apply',mix_apply']; simp only [Pi.star_apply,mix_apply']; unfold Jams.mix; simp_rw [star_sum,star_smul,star_trivial]
lemma moved (x:sun→ F.Coeff)(w:Rung)(m:Motion): Motion.patch F m (Jams.mix w x)= Jams.mix w (fun i=> Motion.patch F m (x i)):=by
   have hh : F.act m.1.ortho (Jams.mix w x)= Jams.mix w (fun i=> F.act m.1.ortho (x i)):= by unfold Jams.mix; simp_rw [aspect,map_sum,map_smul]
   unfold Motion.patch; cases m.2; exact hh; refine (congr_arg star hh).trans ?_; unfold Jams.mix; simp_rw [star_sum,star_smul,star_trivial]; rfl
lemma they {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X](u:ι→sun→ X)(w:Rung)(h:∀ i:sun,Summable (fun k=>u k i)): Jams.mix w (fun i=> ∑' j,u j i)=∑' j, Jams.mix w (u j):=by
   unfold Jams.mix; simp_rw [fun i=>(h i|>.tsum_const_smul (w i)).symm]; rw [Summable.tsum_finsetSum _ ]; exact fun i _=>(h i).const_smul _
-- merge supports. commute because ALL components segmented.
lemma stacking (f:ι→sun→ Coefficient F n)(e:ℕ≃ι×ℕ) (w:Rung) (h:∀ i:sun, Summable (fun j=> (f j i).x))(hv:∀ i:sun,∀ j V,Summable (fun k=> (f k i).forced j V)): weave w (fun i=>Extra.Histories.merge e fun j=>f j i)=Extra.Histories.merge e (fun j=>weave w (f j)):=by
    unfold weave Extra.Histories.merge; dsimp only; congr 1
    · exact they (fun j i=>(f j i).x) w h
    · funext i; rw [mix_apply',mix_apply']
    · funext i V; simp only [mix_apply']; exact they (fun j t=> (f j t).forced i V) w (fun t=> hv t i V)
include h
lemma paidStretch (v:ℂ): Forum (fun i=> Extra.Histories.stretch v (p i)) q (v • y) Y P (‖v‖*a) (‖v‖*b):=by
   refine ⟨h.stuck,h.knows,fun w u ht=>?_,fun w u ht=>?_⟩
   · have hp: Jams.mix w (fun i=> v • (p i).x-v • y)= v • Jams.mix w (fun i=>(p i).x-y):=by
        simp_rw [← smul_sub]; unfold Jams.mix; rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _=>smul_comm ..)
     change F.coeffSize (Jams.mix w (fun i=> v • (p i).x-v • y))≤ _; rw [hp,Size.smul]
     exact (mul_le_mul_of_nonneg_left (h.burns w u ht) (norm_nonneg _)).trans_eq (mul_left_comm ..)
   rw [twisted w]; exact ⟨stretch_format v (h.earns w u ht).1,(mul_left_comm ‖v‖ u b) ▸ stretch_rem v (h.earns w u ht).2⟩
lemma whorls (m:Motion)(x:P.orient.activities.Moves m.1 0)(B:SectionData F)(hc:B.Sound Y)(hf:2≤ n.val): Forum (fun i=> audition x (p i)) q (Motion.patch F m y) Y P (orbitCost F*a) (turnCost P.orient.p.order P.orient.p.power*b):=by
   refine ⟨fun i=> turn_same _ _ _ _ (h.stuck i),h.knows,fun w u ht=>?_, fun w u ht=>?_⟩
   · have hh i: (audition x (p i)).x-Motion.patch F m y = Motion.patch F m ((p i).x-y):=by rw [patch_sub]; unfold audition Motion.patch;split<;> rfl
     simp_rw [hh]; rw [← moved]; apply (patch_cost ..).trans; exact (mul_le_mul_of_nonneg_left (h.burns w u ht) (zero_le_one.trans (orbitCost_one_le F))).trans_eq (mul_left_comm ..)
   rw [← moveWeave w m x h.stuck]; obtain ⟨hF,h,-⟩:= Hue.priceU m x B hc hf (h.earns w u ht).1 (h.earns w u ht).2
   rw [mul_left_comm] at h; exact ⟨hF,h⟩
end algebra
lemma multi [Nonempty ι][Countable ι](f:ι→sun→ Coefficient F n)(o:ℕ≃ι×ℕ)(Y:Hol G)(P:Desk G n)(y:ι→F.Coeff)(v t:ι→ℝ)(ht: Summable t)(hv:Summable v)(hY:Summable (fun i=> F.coeffSize (y i)))(h:∀ i,Forum (f i) q (y i) Y P (v i) (t i)): Forum (fun i=>Extra.Histories.merge o fun j=>f j i) q (∑' i,y i) Y P (∑' i,v i) (∑' i,t i):=by
   have he (s:sun)(i):= h i|>.play s
   have h0 : 1≤q:= (h (Classical.arbitrary _)).knows
   have hh (s:sun): Summable (fun i=>(f i s).x-y i):= by
       apply Summable.of_norm; apply Size.series F; apply Summable.of_nonneg_of_le (fun i=> Work.G08.size_nonneg F _) _ hv; exact fun i=>(he s i).1
   have hz (s:sun): Summable (fun i=>(f i s).x):=by simpa only [sub_add_cancel] using (hh s|>.add ((Size.series _ hY).of_norm))
   have hf(t:sun)(j:ℕ) (V:Config G n): Summable fun i=>(f i t).forced j V:= (merge_budget o _ P.sane (fun i=> (he t i).2.2) ht|>.2.2|>.summable V).prod_symm.prod_factor j
   refine ⟨fun _=> funext (fun i=>congr_fun ((h ((o i).1)).stuck _) ((o i).2)),h0,fun w η hη=>?_,fun w η hη=>?_⟩
   · change F.coeffSize (Jams.mix w (fun i=> (∑' j,(f j i).x)-∑' j,y j)) ≤ _
     let u(i):sun→ F.Coeff:=fun s=> (f i s).x-y i
     simp_rw [fun s=> (hz s|>.tsum_sub (Size.series F hY|>.of_norm)).symm]; rw [show Jams.mix w (fun s=> ∑' j,u j s)=_ from they u w hh]; let V(i):=Jams.mix w (u i)
     have hs: Summable (fun i=>F.coeffSize (V i)):= .of_nonneg_of_le (fun i=> Work.G08.size_nonneg F _) (fun i=> (h i).burns w η hη) (hv.mul_left η)
     exact (Size.bound F hs).trans ((hs.tsum_le_tsum (fun i=> (h i).burns w η hη) (hv.mul_left η)).trans_eq tsum_mul_left)
   rw [stacking f o w hz hf]; have h'(i):= (h i).earns w η hη; refine ⟨ merge_format _ _ (fun i=> (h' i).1),?_⟩
   rw [← tsum_mul_left]; exact (merge_budget o _ P.sane (fun i=>(h' i).2) (ht.mul_left η)).1
end Forum
end YM.FullVolume.Paint.Tower
