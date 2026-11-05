import YM.FullVolume.Spiral.Forum
import YM.FullVolume.Luna.Table
/- Epics transfers to Ribbon prices. phase includes fixed File tape only up. Keep.Compression actual.Frame.Y. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Tower
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n m:Side}{Y:Hol G}{ι:Type}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna
variable {i:ℕ}{F:Labels.Frame G i}{B:BudgetPoint}{q t v a b s c:ℝ}{p:sun→ Coefficient F n}{P:Desk G n}{y:F.Coeff}
local notation "A_"=> P.orient
-- pull parse q
set_option maxHeartbeats 390000
open Forum
lemma serum (f:sun→ Pin F n)(k:sun→ Response G n)(hP:t ≤ q) (ht:1 ≤ t)
   (h:LanternX G F P.orient.p q t (Local.patch P.orient.activities) f y a b (P.k*v) k c) (he:∀ s,(Matric.tell (f s)).Format 0 Y P.orient):Forum (fun s=>Matric.tell (f s)) t y Y P a (b+v):=by
   obtain ⟨z,hx,hf⟩:= h.joys.funds; have hh : 0≤ b:= by obtain ⟨a,hA,-⟩:= h.gifts.lamps; exact sumBudget_credit hA
   have hp : 0≤ v:= nonneg_of_mul_nonneg_right (sumBudget_credit hx) P.sane
   refine ⟨fun _=>rfl,ht,fun w u hu=> (le_mul_of_one_le_left (Work.G08.size_nonneg F _) (orbitCost_one_le F)).trans (h.axes w _ (Jams.stripe_down hu (by linarith) hP)),fun w u hu=>?_⟩
   let M:=weave w (fun s=>Matric.tell (f s)); change M.Format _ _ _ ∧ M.remBound ..
   have ht: M=Matric.tell (∑ i∈w.support, (w i:ℂ) • f i):=by
       unfold M weave Matric.tell book; congr 1
       · rw [Prod.fst_sum]; unfold Jams.mix;apply sum_congr rfl; exact fun i _=> aspect
       · rw [Prod.snd_sum,Prod.fst_sum]; unfold Jams.mix;apply sum_congr rfl; intro i _; funext k; exact saneF (s:=w i) (x:=(f i).2.1 k)
       · rw [Prod.snd_sum,Prod.snd_sum]; unfold Jams.mix; apply sum_congr rfl; intro i _; funext k; exact saneF (s:=w i) (x:=(f i).2.2 k)
   obtain ⟨r,hr,hV⟩:= h.gifts.takes hu
   have he₀:= br_scale hx (stripe_pos hu)
   have hT : A_ |> fun A=> Brill A.p (mapSeat (n:=n)) r (A.p.supportExponent) (u*b):=by
       refine Local.sumBudget_mono hr (fun i=>mul_nonneg (Real.exp_pos _).le (hV i).1) (fun i=>mul_le_mul_of_nonneg_right ?_ (hV i).1) le_rfl
       apply Real.exp_le_exp.mpr; apply mul_le_mul_of_nonneg_right (by linarith only) (by positivity)
   rw [← mul_left_comm P.k] at he₀
   refine ⟨ht ▸ formatPin_sum _ he, u*b,u*v, mul_nonneg (stripe_pos hu) hh,mul_nonneg (stripe_pos hu) hp,(mul_add ..|>.symm.le),P.sane,⟨r,hT,hV⟩,u • z,he₀, fun i=>⟨mul_nonneg (stripe_pos hu) (hf i 1|>.nonneg),fun V=>?_⟩⟩
   change ‖Jams.mix w (fun i=> (Matric.tell (f i)).forced) i V‖ ≤ _; rw [mix_apply',mix_apply']; exact mix_d _ hu (hf i V)
lemma field0 (V:Desk G n)(F:Labels.Frame G i)(q:ℝ)(hq: 1 ≤ q) (Y:Hol G): Forum (fun _=> Matric.tell (0:Pin F n)) q 0 Y V 0 0:=by
   suffices ht:Forum (fun s=> Matric.tell (0:Pin F n)) q 0 Y V 0 (0+0) by simpa using ht
   refine serum (q:=q) (fun _=>0) (fun _=>0) (le_refl q) hq (v:=0) (c:=0) ?_ ?_
   · simpa only [mul_zero,add_zero] using noMotion (B:=V.orient.p) (k:= Local.patch V.orient.activities) (t:=0) (s:=0) (p:=q) (F:=F) (r:=0) (v:=0) le_rfl le_rfl le_rfl le_rfl hq
   intro i
   have h:= Coin.wealth (0:Coin F Y V)|>.1; rw [map_zero] at h; exact h
section meristem
variable (Z:sun→Plate F m n)
-- DX formatting real duty
structure Scan (Z:Plate F m n) (A:Hol G)(S:Rep G n)(T:Rep G m):Prop where
   main j : (Matric.tell (Z.main j)).Format 0 A S
   reg j f a : RegFit T 0 i A (mapSeat j) f→ T.p.supBounds 0 (mapSeat j) f a→ (Matric.tell (Z.tint j f)).Format 0 A S
   hard j f (v:ℝ): SlotFit T 0 j f → (∀ V,‖f V‖ ≤ v)→ (Matric.tell (Z.ink j f)).Format 0 A S
variable {U:sun→Rep G n}{K:sun→Rep G m}{Q: Desk G m}
open Extra.Histories.InputColumn
local notation "ι"=> Extra.Histories.InputColumn.Listing
variable (D:Tableau q 300) (E:Heading F)(L:Side)
-- real reads URI
local notation "L_"=> fun (i':F.Index)=> Size.axis F i'
variable {Y':sun→F.Index→ Response G n}{Yr Yk:sun→ℕ→ (Config G m→ℂ)→ Response G n}
variable {η χ :ℝ}
variable (hU:∀ s,Along P.orient (U s))(hK:∀ s,Along Q.orient (K s))(h:Epics Z U K E L Y D P.k Q.k η χ Y' Yr Yk) (hQ:4≤q) (hF :∀ s,Scan (Z s) Y (U s) (K s))
-- helper map turns
local notation "T'"=> q/2
local notation "tp"=> D.price
local notation "p_"=> P.orient
section ep
include hF hQ h hU
lemma herbs (j:F.Index): let x:= Size.axis F j; let b':=η * F.coeffSize (F.core x); let v':=χ*F.coeffSize (vowel F L (F.core x))
   Forum (fun s:sun=> Matric.tell ((Z s).main j)) (q/2) (E.leads L x) Y P ((tp+1)*b') (((tp+1)+(3+2*tp))*v'):=by
   intro x b v'; rw [add_mul (D.price+1) (3+2*D.price)]
   refine serum (fun s=> (Z s).main j) (fun s=>Y' s j) (by linarith only [hQ] : q/2 ≤ q) (by linarith only [hQ]) (c:=2*(tp+1)*v') ?_ (fun s=> along_format _ (hU s).sym (hF s|>.main j))
   rw [ (hU tip).price,show Local.patch P.orient.activities=Local.patch (U tip).activities from (by unfold Local.patch; rw [(hU tip).force])]
   exact h.main j
-- layouts fixed
include hK
lemma regs (f:Coefficient F m)(j:ℕ)(hx: f.Format 0 Y Q.orient) (x:ℝ)(he:Q.orient.p.supBounds 0 (f.support j) (f.regular j) x)(ht:f.support j=mapSeat j) : let v':=η*(Q.orient.p.mass (f.support j) x)
   Forum (fun s:sun=> Matric.tell ((Z s).tint j (f.regular j))) (q/2) 0 Y P ((tp+1)*v') (((tp+1)+(3+2*tp))*v'):=by
   intro v'; have H i: (K i).p.supBounds 0 (mapSeat j) (f.regular j) x:= (hK i|>.price) ▸ ht ▸ he
   have Hv i': RegFit (K i') 0 i Y (mapSeat j) (f.regular j):=ht ▸ (let h':=along_format _ (hK i') hx; show RegFit (K i') 0 _ Y (f.support j) (f.regular j) from ⟨h'.smooth _,h'.origin _,h'.identity_null _,h'.projects _⟩) -- edit .dimension
   rw [add_mul (D.price+1) (3+2*D.price)]; refine serum (fun s:sun=> (Z s).tint j (f.regular j)) (fun s:sun=> Yr s j (f.regular j)) (q:=q) (by linarith only [hQ]) (by linarith only [hQ]) (c:=2*(tp+1)*v') ?_ (fun s=>along_format _ (hU s).sym (hF s|>.reg j (f.regular j) x (Hv s) (H s)))
   unfold v'; rw [(hK tip).price,ht]; rw [(hU tip).price,show Local.patch P.orient.activities=Local.patch (U tip).activities from (by unfold Local.patch; rw [(hU tip).force])]; exact h.reg j _ x (Hv _) (H _)
lemma prints (f:Coefficient F m)(j:ℕ)(hx: f.Format 0 Y Q.orient) (x:ℝ)(hp:0≤x)(he:∀ V, ‖f.forced j V‖≤ x) : let v':=η*(Q.orient.p.mass (Local.patch Q.orient.activities j) x / Q.k)
   Forum (fun s:sun=> Matric.tell ((Z s).ink j (f.forced j))) (q/2) 0 Y P ((tp+1)*v') (((tp+1)+(3+2*tp))*v'):=by
   intro v'; have H i:= along_format _ (hK i) hx
   have Hv i:SlotFit (K i) 0 j (f.forced j):= let h':=H i; ⟨h'.invariant _,h'.borel _,h'.supported _,h'.carried _,h'.forcing _⟩
   rw [add_mul (D.price+1) (3+2*D.price)]; refine serum (fun s:sun=> (Z s).ink j (f.forced j)) (fun s:sun=> Yk s j (f.forced j)) (q:=q) (by linarith) (by linarith only [hQ]) (c:=2*(tp+1)*v') ?_ (fun s=> along_format _ (hU s).sym (hF s|>.hard j _ x (Hv s) he))
   unfold v'; rw [(hK tip).price,show Local.patch Q.orient.activities=Local.patch (K tip).activities from (by unfold Local.patch; rw [(hK tip).force]),(hU tip).price,show Local.patch P.orient.activities=Local.patch (U tip).activities from (by unfold Local.patch; rw [(hU tip).force])]; exact h.hard j _ x (Hv _) hp he
end ep
end meristem
end YM.FullVolume.Paint.Tower
