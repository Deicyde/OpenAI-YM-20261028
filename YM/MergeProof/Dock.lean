import YM.MergeProof.Prism
import YM.MergeProof.Zing
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Accent Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories Planned.GuardedAtom
variable {t d p e a c':ℝ} {o: V→Site f}{w:V→ℝ}
-- does require blank slots; global dormant. True on current history. memory uses barcode not wing for outputs.
structure Arsenal (R:Rep G f): Prop where
   dry (p:Support f): p.Nonempty → ∃ j, (R.activities.reg j).support=p ∧ R.activities.E j=0
   wet (p:Box f): Sure p → ∃ j,barcode R.activities j=p ∧ ∀ U,p.1 ∩ RG.flags R.p.threshold U=p.2 → (R.activities.forced j).eligible R.p.threshold U

variable {T:BudgetPoint} {K:Support f→ Config G f→Poly B} {F:Box f→ Config G f→Poly B}
lemma Offer.cross [Fintype ι][Fintype β]{q:ι→Hat B R}{r:β→Hat B R}{b:ℕ}(h:Offer o q w b e d)(hp:Offer o r w b e a): Offer o (Sum.elim q r) w b e (d+a):=by
   refine ⟨fun i=>match i with | .inl i=> h.sites i| .inr i=>hp.sites i,fun i=>?_⟩
   refine ⟨fun j=> ?_,Summable.of_finite,?_⟩
   · cases j; exact (h.budget i).1 _; exact (hp.budget i).1 _
   rw [tsum_fintype,Fintype.sum_sum_type]; exact add_le_add (Extra.Multi.Budget.cap (h.budget i) _) (Extra.Multi.Budget.cap (hp.budget i) _)

lemma drydock (h : Carton o K F R.p.threshold)(he:Towed w id K R.p.B d a)(hq:Towed w (fun i:Box f=>i.1) F R.p.B d a)(hw:∀ i,0<w i)(hx:Arsenal R):
   ∃ (I:Type) (_:Fintype I)(q:I→Hat B R), (∀ i,2 ≤ (q i).s.val.card) ∧ Offer o q w R.p.B d (4*a) ∧ (∀ U,(∑ i,odour (q i) U)=∑ i,K i U)∧∀ i U,∑ j,fragrance (q j) U i=F i U:=by
   have hb(i): K i≠0→i.Nonempty:=by
      intro H; obtain ⟨U,hU⟩:= Function.ne_iff.mp H; obtain ⟨p,hp⟩:= Function.ne_iff.mp (show Poly.part (K i U) ≠ Poly.part 0 from (by intro g; exact hU g)); let y:= h.exp i; have ht: 2 ≤ p.val.card:= y.2 U _ hp; exact ((Finset.card_pos.mp (by omega : 0 < p.val.card)).image o).mono (y.1.toBorne.place _ _ hp)
   let k(i:Support f) := if H:K i≠0 then (hx.dry i (hb i H)).choose else 0
   let g i:= Wing.logKey (k i); have hK (i)(he:K i≠0): (R.activities.reg (k i)).support=i ∧ R.activities.E (k i)=0:=by unfold k; rw [dif_pos he]; exact (hx.dry i (hb i he)).choose_spec
   have hv(i U)(he:K i U≠0): (g i).qualifies R U:=by change Healthy _ _ U; rw [(hK i (fun hh=> he (congr_fun hh U))).1]; exact ((h.exp i).1.permits U he)
   obtain ⟨N,hN,H,hn⟩:= alarm w hw (F:=K) (X:=id) (g:=g) (fun i hp=> hK i hp) hv (fun i=>(h.exp i).1.toBorne) (fun i=>(h.exp i).2) he
   have hd(i): F i≠0 → Sure i:=by intro hh; obtain ⟨U,hU⟩:= Function.ne_iff.mp hh; exact ((h.flag i).1.permits U hU).2
   let L(i: Box f):= if H:F i≠0 then (hx.wet i (hd i H)).choose else 0
   let l i:= Wing.gasKey (L i); have hF(i)(h:F i≠0): barcode R.activities (L i)=i ∧ ∀ U,i.1∩RG.flags R.p.threshold U=i.2 → (R.activities.forced (L i)).eligible R.p.threshold U:=by unfold L; rw [dif_pos h]; exact (hx.wet i (hd i h)).choose_spec
   have ht (i U)(he:F i U≠0): (l i).qualifies R U:=(hF i (fun hh=> he (congr_fun hh U))).2 U (((h.flag i).1.permits U he).1)
   obtain ⟨M,hM,hB,hm⟩:= alarm w hw (F:=F) (X:=Prod.fst) (g:=l) (fun i hp=> ⟨(Prod.mk.inj (hF i hp).1).1,trivial⟩) ht (fun i=>(h.flag i).1.toBorne) (fun i=>(h.flag i).2) hq
   let m:= Sum.elim N M
   have hp(x): (N x).M.turn= .logKey (k x.1):= (hN x).1; have ht(x): (M x).M.turn=.gasKey (L x.1):=(hM x).1
   have hk(i:VividId F):barcode R.activities (L i.1)=i.1:=(hF _ (fun H=> (show Vivid F i.1 i.2.1.val from i.2.1.property).elim (fun U hU=> hU (by rw [H]; rfl)))).1
   have hy(U x):odour (N x) U=amount (N x) U:=by unfold odour prose; rw [hp,varnish]
   have hx'(U x):odour (M x) U=0:=by unfold odour prose;simp [ht]
   have hz (U x i):fragrance (N x) U i=0:=by unfold fragrance entry; simp [hp]
   have hs(U x i):fragrance (M x) U i=if x.1=i then amount (M x) U else 0:=by unfold fragrance entry; rw [ht]; dsimp only; rw [hk]; split_ifs; exact (varnish ..).symm; simp
   refine ⟨_,inferInstance,m,fun i=> ?_,by rw [show 4*a= _ from (show 4*a=2*a+2*a by ring)]; exact H.cross hB,fun U=> ?_,fun i U=> ?_⟩
   · cases i with
     | inl i=> unfold m; simp only [Sum.elim_inl,(hN i).2]; exact (h.exp i.1).2 _ _ i.2.1.property.choose_spec
     | inr i=> unfold m; simp only [Sum.elim_inr,(hM i).2]; exact (h.flag i.1).2 _ _ i.2.1.property.choose_spec
   · unfold m; rw [Fintype.sum_sum_type]; simp_rw [Sum.elim_inl, Sum.elim_inr, hy,hx', Finset.sum_const_zero,add_zero]; rw [Fintype.sum_sigma]; exact sum_congr rfl fun i _=> hn i U
   unfold m; rw [Fintype.sum_sum_type]; simp_rw [Sum.elim_inl,Sum.elim_inr,hz,Finset.sum_const_zero,zero_add,hs]; rw [Fintype.sum_sigma,sum_eq_single i]
   · simpa only [↓reduceIte] using hm i U
   · intro j _ hj; simp only [hj,↓reduceIte,sum_const_zero]
   simp
end YM.MergeProof.Menu
